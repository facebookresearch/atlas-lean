/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GlobalSemistableSkeleton
public import MathlibExt.AlgebraicGeometry.AnalyticTropicalSupport
public import MathlibExt.AlgebraicGeometry.IntegralTropicalCycles
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.GroupTheory.Index

/-!
# Actual skeletal torus coordinates and degree/index sums

The torus map is a scheme morphism from the actual boundary complement.
Coordinates are the Laurent-character evaluations of its native Berkovich
point map. Integral slopes are literal coefficient/exponent formulas on
actual adapted Gauss cells. The induced lattice homomorphism is computed
from those exponents; its index is inside the actual target facet lattice.
The degree is the dimension of the actual generic-fibre section algebra
over the actual target generic-point residue field.

Reference: Gubler--Rabinoff--Werner, 1404.7044v3, sections 4/8,
Proposition 8.2 and Theorem 8.4. The normalized affine slope/cell
construction and degree comparison remain direct Wanted results.
Native generic fibres/residue fields and integer indices are Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, Apache 2.0.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SkeletalTropicalDegree

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry TopologicalSpace
open SemistableFormalAtlas GlobalSemistableSkeleton BerkovichAnalytification
open ValuativeTropicalization
open scoped BigOperators

variable {K : Type} [NormedField K] [IsUltrametricDist K]
  (P : StrictPair K) (A : GlobalAtlas P)

def boundaryEmbedding (C : StandardEtaleChart K P.model) : Fin (C.r + 1 + C.s) ↪ Fin C.n where
  toFun j := ⟨j.val, j.isLt.trans_le C.bound⟩
  inj' := by
    intro i j h
    exact Fin.ext (congrArg (fun z : Fin C.n ↦ z.val) h)

structure AdaptedCell (S : GlobalStratum P) where
  chart : StandardEtaleChart K P.model
  dimension : chart.n = P.dimension + 1
  comparison : ChartComparison P chart
  stratum : SemistableFormalAtlas.Stratum chart
  fullVanishing : stratum.vanishing = Finset.univ.image (boundaryEmbedding P chart)
  sourceGeneric : comparison.specialMap stratum.genericPoint.val = S.genericPoint.val
  reductionCompatibility : ∀ q,
    A.reduction (comparison.map q) = comparison.specialMap (comparison.reduction.map q)
  interior : {p : AnalyticPoint P | p ∈ skeleton P A ∧ A.reduction p = S.genericPoint.val} =
    comparison.map '' {q | IsGaussPoint chart comparison.reduction stratum q q}

variable (F : ∀ S : GlobalStratum P, AdaptedCell P A S)

def cellLattice (S : GlobalStratum P) :
    AddSubgroup (Fin ((F S).chart.r + 1 + (F S).chart.s) → ℤ) where
  carrier := {u | (∑ j : Fin ((F S).chart.r + 1), u ⟨j.val, by omega⟩) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Finset.sum_add_distrib] at hu hv ⊢
    rw [hu, hv, add_zero]
  neg_mem' := by
    intro u hu
    simp only [Set.mem_ofPred_eq, Pi.neg_apply, Finset.sum_neg_distrib] at hu ⊢
    rw [hu, neg_zero]

def cellDimension (S : GlobalStratum P) : ℕ := (F S).chart.r + (F S).chart.s

variable (m : ℕ) (I : Ideal (ValuativeTropicalization.CoordinateRing K m))
  (phi : complementScheme P ⟶ ValuativeTropicalization.subscheme I)

def torusVector (p : BerkovichAnalytification.Point K (complementScheme P)) :
    FiniteToricCoordinates.RealSpace m :=
  AnalyticTropicalSupport.valuationVector K m I (BerkovichAnalytification.mapPoint phi p)

theorem torusVector_mem (p : BerkovichAnalytification.Point K (complementScheme P)) :
    torusVector P m I phi p ∈ AnalyticTropicalSupport.tropicalization K m I :=
  subset_closure ⟨BerkovichAnalytification.mapPoint phi p, rfl⟩

def skeletalDomain : Set (BerkovichAnalytification.Point K (complementScheme P)) :=
  {p | BerkovichAnalytification.mapPoint (complementInclusion P) p ∈ skeleton P A}

def skeletalImage : Set (FiniteToricCoordinates.RealSpace m) :=
  torusVector P m I phi '' skeletalDomain P A

theorem domainPoint_open (p : BerkovichAnalytification.Point K (complementScheme P)) :
    (BerkovichAnalytification.mapPoint (complementInclusion P) p).schemePoint ∈ complementOpen P :=
  p.schemePoint.property

def retractedDomain (R : GlobalRetraction P A)
    (p : BerkovichAnalytification.Point K (complementScheme P)) :
    BerkovichAnalytification.Point K (complementScheme P) :=
  A.domainLift (R.map (BerkovichAnalytification.mapPoint (complementInclusion P) p))
    (R.preserves_complement _ (domainPoint_open P p))

structure IntegralSlopes where
  coefficient : ∀ _S : GlobalStratum P, Fin m → Kˣ
  exponent : ∀ S : GlobalStratum P,
    Fin m → Fin ((F S).chart.r + 1 + (F S).chart.s) → ℤ
  normalized : ∀ (S : GlobalStratum P) (q : (F S).chart.model.GenericPoint)
      (h : ((F S).comparison.map q).schemePoint ∈ complementOpen P),
    IsGaussPoint (F S).chart (F S).comparison.reduction (F S).stratum q q →
    ∀ i : Fin m,
      torusVector P m I phi (A.domainLift ((F S).comparison.map q) h) i =
        -Real.log ‖(coefficient S i : K)‖ +
          ∑ j, (exponent S i j : ℝ) * (-Real.log (coordinateNorm (F S).chart q
            (boundaryEmbedding P (F S).chart j)))

variable (L : IntegralSlopes P A F m I phi)

def latticeHom (S : GlobalStratum P) : cellLattice P A F S →+ (Fin m → ℤ) where
  toFun u := fun i ↦ ∑ j, L.exponent S i j * u.val j
  map_zero' := by ext i; simp
  map_add' u v := by ext i; simp [mul_add, Finset.sum_add_distrib]

def latticeIndex (tau : IntegralTropicalCycles.Polyhedron m) (S : GlobalStratum P) : ℕ :=
  ((latticeHom P A F m I phi L S).range.comap tau.lattice.subtype).index

def activeStrata (w : FiniteToricCoordinates.RealSpace m) : Set (GlobalStratum P) :=
  {S | cellDimension P A F S = P.dimension ∧
    ∃ p : BerkovichAnalytification.Point K (complementScheme P),
      BerkovichAnalytification.mapPoint (complementInclusion P) p ∈ stratumCell P A S ∧
        torusVector P m I phi p = w}

def cellTropicalImage (S : GlobalStratum P) : Set (FiniteToricCoordinates.RealSpace m) :=
  {w | ∃ p : BerkovichAnalytification.Point K (complementScheme P),
    BerkovichAnalytification.mapPoint (complementInclusion P) p ∈ stratumCell P A S ∧
      torusVector P m I phi p = w}

def cellImageDimension (S : GlobalStratum P) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ (cellTropicalImage P A m I phi S)).direction

def indexSum (tau : IntegralTropicalCycles.Polyhedron m)
    (w : FiniteToricCoordinates.RealSpace m) : ℕ := by
  classical
  letI : Finite (GlobalStratum P) := A.strataFinite
  letI := Fintype.ofFinite (GlobalStratum P)
  exact ∑ S : GlobalStratum P, if S ∈ activeStrata P A F m I phi w then
    latticeIndex P A F m I phi L tau S else 0

def GenericTargetPoint (w : FiniteToricCoordinates.RealSpace m) : Prop :=
  ∀ S : GlobalStratum P, cellImageDimension P A m I phi S < P.dimension →
    w ∉ cellTropicalImage P A m I phi S

variable [I.IsPrime]

instance targetIntegral : IsIntegral (ValuativeTropicalization.subscheme I).left := by
  change IsIntegral (Spec (CommRingCat.of (ValuativeTropicalization.CoordinateRing K m ⧸ I)))
  infer_instance

abbrev targetGeneric := genericPoint (ValuativeTropicalization.subscheme I).left

abbrev GenericResidue := (ValuativeTropicalization.subscheme I).left.residueField
  (targetGeneric m I)

def genericFibre : Scheme := pullback phi.left
  ((ValuativeTropicalization.subscheme I).left.fromSpecResidueField (targetGeneric m I))

def genericProjection : genericFibre P m I phi ⟶ Spec (CommRingCat.of (GenericResidue m I)) :=
  pullback.snd phi.left
    ((ValuativeTropicalization.subscheme I).left.fromSpecResidueField (targetGeneric m I))

def genericScalar : GenericResidue m I →+* Γ(genericFibre P m I phi, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (GenericResidue m I))).inv ≫
    (genericProjection P m I phi).appTop).hom

structure GenericallyFinite : Prop where
  dense : DenseRange phi.left
  finite : IsFinite (genericProjection P m I phi)
  finiteVector : letI := (genericScalar P m I phi).toAlgebra
    Module.Finite (GenericResidue m I) Γ(genericFibre P m I phi, ⊤)

/-- The generic degree of a generically finite map: the dimension of the functions on the generic
fibre over the residue field of the generic point. Without the finiteness witness this `finrank`
would silently be `0` for an infinite-dimensional generic fibre. -/
@[nolint unusedArguments]
def genericDegree (_finite : GenericallyFinite P m I phi) : ℕ := by
  letI := (genericScalar P m I phi).toAlgebra
  exact Module.finrank (GenericResidue m I) Γ(genericFibre P m I phi, ⊤)

end MathlibExt.AlgebraicGeometry.SkeletalTropicalDegree
