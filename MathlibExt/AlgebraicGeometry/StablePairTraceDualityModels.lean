/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StablePairTraceModels
public import MathlibExt.AlgebraicGeometry.StablePairCochainTensorMaps

/-!
# Native graded duals and the trace adjunction mate

The dual terms are actual sheaf Homs to the structure module, with
the dg dual differential. The tensor-to-endomorphism comparison is
fixed on every local rank-one operator, including its Koszul sign.
Evaluation with any coefficient complex is fixed on all triple pure
tensors. These formulas normalize the counit of the adjunction of
the two actual derived tensor functors.

The trace mate is that adjunction's transpose composed with the
normalized tensor-to-Hom inverse. It is not a supplied Ext functional.

Reference: Pandharipande–Thomas, arXiv:0707.2348v5, §2.3,
the trace splitting and the passage from (2.12) to (2.13).
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StablePairTraceDualityModels

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open FourierMukai BundleTrace CoherentCurveLinearSeries
open StablePairPerfectComplexes StablePairTraceModels StablePairInternalHomMaps
open StablePairCochainTensorMaps NormalizedModuleTensorMaps
attribute [local instance] HasDerivedCategory.standard

variable {Y : Scheme} (A : FiniteComplex Y)

/-- The actual graded dual term. -/
def dualDegree (n : ℤ) : Y.Modules := homSheaf Y (A.cochain.X (-n)) (structureModule Y)

/-- The native dg dual differential is -(-1)^n times precomposition. -/
def dualDifferential (n : ℤ) : dualDegree A n ⟶ dualDegree A (n+1) :=
  (-(Int.negOnePow n).val) • precompose (A.cochain.d (-(n+1)) (-n))

def DualSquaredZero : Prop := ∀ n : ℤ, dualDifferential A n ≫ dualDifferential A (n+1) = 0

def dualComplex (h : DualSquaredZero A) : Cochains Y :=
  CochainComplex.of (dualDegree A) (dualDifferential A) h

/-- Evaluation of the literal localized sheaf-Hom at the terminal slice object. -/
def localHom {M N : Y.Modules} (U : Y.Opens) (f : Γ(homSheaf Y M N,U))
    (x : Γ(M,U)) : Γ(N,U) :=
  f.app (op (Over.mk (𝟙 U))) x

/-- The all-degree tensor-to-Hom comparison is fixed on every actual rank-one operator. -/
structure EndTensorComparison (hd : DualSquaredZero A) (he : EndSquaredZero A) where
  map : (cochainTensor Y).obj (dualComplex A hd,A.cochain) ⟶ endComplex A he
  [quasiIso : QuasiIso map]
  normalized : ∀ (j l : Indices A) (n : ℤ) (U : Y.Opens)
    (f : Γ(dualDegree A (-j.val),U)) (a : Γ(A.cochain.X (j.val+n),U))
    (v : Γ(A.cochain.X l.val,U)),
    localHom U
      ((Pi.π (fun q : Indices A =>
        homSheaf Y (A.cochain.X q.val) (A.cochain.X (q.val+n))) l).app U
        ((map.f n).app U
          ((tensorInsertion (dualComplex A hd) A.cochain (-j.val) (j.val+n) n
              (by omega)).app U
            (pureTensorSection Y (dualDegree A (-j.val)) (A.cochain.X (j.val+n)) U f a))))
      v =
      if h : l = j then
        (Int.negOnePow (j.val * (j.val+n))).val •
          (show Γ(Y,U) from localHom U f
            ((A.cochain.XIsoOfEq (p := l.val) (q := -(-j.val)) (by simp [h])).hom.app U v)) •
              ((A.cochain.XIsoOfEq (p := j.val+n) (q := l.val+n) (by simp [h])).hom.app U a)
      else 0

attribute [instance] EndTensorComparison.quasiIso

/-- The actual local triple tensor in the nested totalization. -/
def nestedTensorGenerator (hd : DualSquaredZero A) (L : Cochains Y)
    (i j k n : ℤ) (h : i + (j+k) = n) (U : Y.Opens)
    (f : Γ(dualDegree A i,U)) (a : Γ(A.cochain.X j,U)) (l : Γ(L.X k,U)) :
    Γ(((cochainTensor Y).obj
      (dualComplex A hd,(cochainTensor Y).obj (A.cochain,L))).X n,U) :=
  (tensorInsertion (dualComplex A hd) ((cochainTensor Y).obj (A.cochain,L))
      i (j+k) n h).app U
    (pureTensorSection Y (dualDegree A i) (((cochainTensor Y).obj (A.cochain,L)).X (j+k))
      U f ((tensorInsertion A.cochain L j k (j+k) rfl).app U
        (pureTensorSection Y (A.cochain.X j) (L.X k) U a l)))

/-- The coefficient evaluation is fixed on all triple tensors, also in the zero-weight degrees. -/
structure CochainEvaluation (hd : DualSquaredZero A) (L : Cochains Y) where
  map : (cochainTensor Y).obj
    (dualComplex A hd,(cochainTensor Y).obj (A.cochain,L)) ⟶ L
  normalized : ∀ (j k : ℤ) (U : Y.Opens)
    (f : Γ(dualDegree A (-j),U)) (a : Γ(A.cochain.X j,U)) (l : Γ(L.X k,U)),
    (map.f k).app U (nestedTensorGenerator A hd L (-j) j k k (by omega) U f a l) =
      (show Γ(Y,U) from localHom U f
        ((A.cochain.XIsoOfEq (p := j) (q := -(-j)) (by omega)).hom.app U a)) • l
  other_normalized : ∀ (i j k n : ℤ) (h : i + (j+k) = n) (_hne : i+j ≠ 0)
    (U : Y.Opens) (f : Γ(dualDegree A i,U)) (a : Γ(A.cochain.X j,U)) (l : Γ(L.X k,U)),
    (map.f n).app U (nestedTensorGenerator A hd L i j k n h U f a l) = 0

variable [HasDerivedTensors.{0}]

/-- The nested tensor comparison uses the native two-variable derived counit twice. -/
def nestedTensorCounit (hd : DualSquaredZero A) (L : Cochains Y) :
    (derivedTensorUncurried Y).obj
      (DerivedCategory.Q.obj (dualComplex A hd),
        (derivedTensorUncurried Y).obj
          (DerivedCategory.Q.obj A.cochain,DerivedCategory.Q.obj L)) ⟶
      DerivedCategory.Q.obj ((cochainTensor Y).obj
        (dualComplex A hd,(cochainTensor Y).obj (A.cochain,L))) :=
  (derivedTensorUncurried Y).map
    (𝟙 (DerivedCategory.Q.obj (dualComplex A hd)), tensorCounit Y A.cochain L) ≫
      tensorCounit Y (dualComplex A hd) ((cochainTensor Y).obj (A.cochain,L))

/-- The actual perfect-tensor adjunction is normalized by all coefficient evaluations. -/
structure PerfectTensorAdjunction (hd : DualSquaredZero A) where
  adjunction : (derivedTensor Y).obj (DerivedCategory.Q.obj (dualComplex A hd)) ⊣
    (derivedTensor Y).obj (DerivedCategory.Q.obj A.cochain)
  evaluation : ∀ L : Cochains Y, CochainEvaluation A hd L
  normalized : ∀ L : Cochains Y,
    adjunction.counit.app (DerivedCategory.Q.obj L) =
      nestedTensorCounit A hd L ≫ DerivedCategory.Q.map (evaluation L).map

/-- Transpose the actual Atiyah map through the fixed perfect-tensor adjunction. -/
def traceMate (hd : DualSquaredZero A) (he : EndSquaredZero A)
    (C : EndTensorComparison A hd he) (P : PerfectTensorAdjunction A hd)
    (L : Cochains Y)
    (hTensor : IsIso (tensorCounit Y (dualComplex A hd) A.cochain))
    (α : DerivedCategory.Q.obj A.cochain ⟶
      (derivedTensorUncurried Y).obj
        (DerivedCategory.Q.obj A.cochain, DerivedCategory.Q.obj L)) :
    DerivedCategory.Q.obj (endComplex A he) ⟶ DerivedCategory.Q.obj L := by
  letI := hTensor
  exact inv (DerivedCategory.Q.map C.map) ≫
    inv (tensorCounit Y (dualComplex A hd) A.cochain) ≫
      (P.adjunction.homEquiv (DerivedCategory.Q.obj A.cochain) (DerivedCategory.Q.obj L)).symm α

end MathlibExt.AlgebraicGeometry.StablePairTraceDualityModels
