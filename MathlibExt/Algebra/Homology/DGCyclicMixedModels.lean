/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Algebra.Homology.DGCyclicBarModels
public import MathlibExt.Algebra.Homology.GradedMixedCochainModels
public import Mathlib.Algebra.DirectSum.Module

/-!
# Actual DG Hochschild and Connes totalizations

The Hochschild total term in cohomological degree r is the direct sum
of bar terms C_n in internal degree r+n. Its differential is
(-1)^n d_internal plus the alternating multiplication faces.
Connes' B is the transpose convention (1-t)sN, where
t_n=(-1)^n τ_n and s inserts the unit in front. Every map is computed
from the native bar generators and cochain tensor braiding.

A completed total or mixed model is constrained in every degree and
on every differential. It is not an object freely named Hochschild
homology. Negative cyclic uses the completed product [[u]] model in
GradedMixedCochainModels; ordinary cyclic and its Hodge filtration use
the separate direct-sum u^-1 model.

References: Kaledin, arXiv:math/0611623v4, §1.3 and 1.16--1.17;
Loday, Cyclic homology, §1.1. The Connes convention agrees with the
transpose of TauCeti's completed CyclicCohomology.ConnesOperator at
62bbc0596dc3539d488232e4e924a338548ea0a9. No ungraded cochain theorem
is asserted to supply the DG totalization automatically.
-/

@[expose] public noncomputable section

namespace MathlibExt.Algebra.Homology.DGCyclicMixedModels

open _root_.CategoryTheory MonoidalCategory Limits
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.Algebra.Homology.DGCyclicBarModels
open MathlibExt.Algebra.Homology.GradedMixedCochainModels
open CochainComplex.HomComplex

universe u

variable {k : Type u} [CommRing k]

/-- Canonical reindexing between equal actual cochain degrees. -/
def degreeCast (C : Cochains k) {i j : ℤ} (h : i = j) : C.X i →ₗ[k] C.X j :=
  (eqToHom (congrArg C.X h)).hom

/-- The cohomological Hochschild-total summand. -/
abbrev HochschildSummand (A : DGAlgebra k) (r : ℤ) (n : ℕ) : Type u :=
  (tensorPower A.X (n + 1)).X (r + (n : ℤ))

/-- The literal direct-sum total term, not a supplied homology group. -/
abbrev HochschildValues (A : DGAlgebra k) (r : ℤ) :=
  DirectSum ℕ (HochschildSummand A r)

/-- Native inclusion of the fixed bar-degree summand. -/
def includeHochschild (A : DGAlgebra k) (r : ℤ) (n : ℕ) :
    HochschildSummand A r n →ₗ[k] HochschildValues A r :=
  DirectSum.lof k ℕ (HochschildSummand A r) n

/-- The actual internal differential on a total summand. -/
def internalBlock (A : DGAlgebra k) (r : ℤ) (n : ℕ) :
    HochschildSummand A r n →ₗ[k] HochschildValues A (r + 1) :=
  (includeHochschild A (r + 1) n).comp
    ((degreeCast (tensorPower A.X (n + 1)) (by omega)).comp
      ((tensorPower A.X (n + 1)).d (r + (n : ℤ)) (r + (n : ℤ) + 1)).hom)

/-- The actual alternating Hochschild faces on a total summand. -/
def faceBlock (A : DGAlgebra k) (r : ℤ) : (n : ℕ) →
    (HochschildSummand A r n →ₗ[k] HochschildValues A (r + 1))
  | 0 => 0
  | n + 1 => (includeHochschild A (r + 1) n).comp
      ((degreeCast (tensorPower A.X (n + 1)) (by omega)).comp
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
          ((barFace A n i).f (r + ((n + 1 : ℕ) : ℤ))).hom))

/-- The fixed total differential, determined on every direct-sum generator. -/
def hochschildDifferential (A : DGAlgebra k) (r : ℤ) :
    HochschildValues A r →ₗ[k] HochschildValues A (r + 1) :=
  DirectSum.toModule k ℕ (HochschildValues A (r + 1))
    (fun n => (-1 : ℤ) ^ n • internalBlock A r n + faceBlock A r n)

/-- The signed cyclic rotation on the actual tensor-power term. -/
def signedRotation (A : DGAlgebra k) (n : ℕ) :
    tensorPower A.X (n + 1) ⟶ tensorPower A.X (n + 1) :=
  (-1 : ℤ) ^ n • (cyclicRotation A.X n).hom

/-- Iteration of the same actual signed rotation. -/
def cyclicIterate (A : DGAlgebra k) (n : ℕ) : ℕ →
    (tensorPower A.X (n + 1) ⟶ tensorPower A.X (n + 1))
  | 0 => 𝟙 _
  | i + 1 => cyclicIterate A n i ≫ signedRotation A n

/-- The actual finite cyclic norm 1+t+...+t^n. -/
def cyclicNorm (A : DGAlgebra k) (n : ℕ) :
    tensorPower A.X (n + 1) ⟶ tensorPower A.X (n + 1) :=
  ∑ i ∈ Finset.range (n + 1), cyclicIterate A n i

/-- The extra bar degeneracy is literal unit insertion in front. -/
def extraDegeneracy (A : DGAlgebra k) (n : ℕ) :
    tensorPower A.X (n + 1) ⟶ tensorPower A.X (n + 2) :=
  (λ_ (tensorPower A.X (n + 1))).inv ≫
    (MonObj.one (X := A.X) ⊗ₘ 𝟙 (tensorPower A.X (n + 1)))

/-- The source-normalized chain Connes operator N, then s, then 1-t. -/
def connesBar (A : DGAlgebra k) (n : ℕ) :
    tensorPower A.X (n + 1) ⟶ tensorPower A.X (n + 2) :=
  cyclicNorm A n ≫ extraDegeneracy A n ≫
    (𝟙 (tensorPower A.X (n + 2)) - signedRotation A (n + 1))

/-- The computed total Connes map, of cohomological degree -1. -/
def connesDifferential (A : DGAlgebra k) (r : ℤ) :
    HochschildValues A r →ₗ[k] HochschildValues A (r - 1) :=
  DirectSum.toModule k ℕ (HochschildValues A (r - 1)) (fun n =>
    (includeHochschild A (r - 1) (n + 1)).comp
      ((degreeCast (tensorPower A.X (n + 2)) (by omega)).comp
        ((connesBar A n).f (r + (n : ℤ))).hom))

/-- The actual cochain total, fixed in every term and differential. -/
structure HochschildTotalModel (A : DGAlgebra k) where
  complex : Cochains k
  termIso : ∀ r : ℤ, complex.X r ≅ ModuleCat.of k (HochschildValues A r)
  differential_eq : ∀ r : ℤ,
    complex.d r (r + 1) ≫ (termIso (r + 1)).hom =
      (termIso r).hom ≫ ModuleCat.ofHom (hochschildDifferential A r)

/-- The completed mixed model has the actual Connes map, not an
arbitrary square-zero endomorphism of a supplied cohomology object. -/
structure HochschildMixedModel (A : DGAlgebra k) where
  total : HochschildTotalModel A
  connes : Cochain total.complex total.complex (-1)
  connes_eq : ∀ r : ℤ,
    connes.v r (r - 1) (by omega) ≫ (total.termIso (r - 1)).hom =
      (total.termIso r).hom ≫ ModuleCat.ofHom (connesDifferential A r)
  closed : δ (-1) 0 connes = 0
  square : connes.comp connes (show (-1 : ℤ) + (-1) = -2 from rfl) = 0

/-- The unweighted mixed complex as a constant-weight graded mixed
object. Its NC(0) model is exactly the completed negative-cyclic product. -/
def mixedObject {A : DGAlgebra k} (M : HochschildMixedModel A) : GradedMixed k where
  weight _ := M.total.complex
  epsilon _ := M.connes
  closed _ := M.closed
  square _ := M.square

/-- Actual DG Hochschild homology with the source homological index. -/
def hochschildHomology {A : DGAlgebra k} (M : HochschildTotalModel A) (n : ℤ) :
    ModuleCat.{u} k :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (.up ℤ) (-n)).obj M.complex

end MathlibExt.Algebra.Homology.DGCyclicMixedModels
