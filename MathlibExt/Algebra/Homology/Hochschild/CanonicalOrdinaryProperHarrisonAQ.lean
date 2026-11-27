/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.Hochschild.CanonicalPositiveHochschildAugmentation
public import MathlibExt.Algebra.Homology.Hochschild.CanonicalProperShuffleCotangentComparison
public import MathlibExt.Algebra.Homology.Hochschild.ProperShuffleCotangentAQTarget
public import MathlibExt.Algebra.Homology.Embedding.PositiveNatHomology

/-!
# Proper Harrison homology and canonical André–Quillen homology

Let `k : Type u` be a commutative `ℚ`-algebra, `B : CommAlgCat.{max u v} k`, and `M : Type w`
an additive group with compatible `k`- and `B`-module actions. The proper-shuffle relations
use two strictly positive input degrees. Restricting their quotient complex to positive
degrees gives a complex whose degree `n` corresponds to ordinary quotient degree `n+1`.

The signed total of the canonical positive proper-shuffle bicomplex maps horizontally to this
restricted quotient and vertically to the alternating cotangent diagram. The vertical map is a
quasi-isomorphism; the horizontal map is a quasi-isomorphism when `B` is flat over `k`. Their
induced homology isomorphisms, together with cotangent normalization and scalar restriction,
identify proper Harrison homology in degree `n+1` with canonical André–Quillen homology in
degree `n`, for arbitrary `M`.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite
open scoped TensorProduct Simplicial

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle.Canonical

open AugmentedAlgebra

variable (k : Type u) [kRing : CommRing k] [kRational : Algebra ℚ k] (B : CommAlgCat.{max u v} k)
  (M : Type w) [mAdd : AddCommGroup M] [mGround : Module k M] [mAlgebra : Module B M]
  [mComm : SMulCommClass k B M] [mTower : IsScalarTower k B M]

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive group `M :
Type w` with compatible `k`- and `B`-module actions, `ordinaryProperCotangentComplex k B M` is
`properCotangentComplex k B M`, the positive restriction of `positiveQuotient k B M`. It is a
chain complex in `ModuleCat.{max u v w} k`; its degree `n : ℕ` corresponds to degree `n+1` of
the quotient by shuffles with two strictly positive factors. -/
abbrev ordinaryProperCotangentComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  properCotangentComplex k B M

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive group `M :
Type w` with compatible `k`- and `B`-module actions, the terminal chain complex of
`positiveProperDiagram k B M` is isomorphic to `ordinaryProperCotangentComplex k B M`. The
terminal augmentation is `B ⟶ B`, so its coefficient action is the given `B`-action on `M`,
and the quotient-component maps in this isomorphism are identities. -/
def terminalProperCotangentIso :
    (positiveProperDiagram k B M).right ≅ ordinaryProperCotangentComplex k B M := by
  have hModule : coefficientModule k B M (terminal k B) = mAlgebra :=
    Module.ext' _ _ (fun b m => by rfl)
  let originalPulledComm :=
    letI : Module B M := mAlgebra
    letI : SMulCommClass k B M := mComm
    letI : IsScalarTower k B M := mTower
    coefficientCommutes k B M (terminal k B)
  let originalPulledTower :=
    letI : Module B M := mAlgebra
    letI : SMulCommClass k B M := mComm
    letI : IsScalarTower k B M := mTower
    coefficientTower k B M (terminal k B)
  have h : (positiveProperDiagram k B M).right = ordinaryProperCotangentComplex k B M := by
    change (letI : Module B M := coefficientModule k B M (terminal k B)
      letI : SMulCommClass k B M := originalPulledComm
      letI : IsScalarTower k B M := originalPulledTower
      properCotangentComplex k B M) = ordinaryProperCotangentComplex k B M
    cases hModule
    rfl
  exact eqToIso h

/-- For a commutative `ℚ`-algebra `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive
group `M : Type w` with `Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower
k B M`, let `T = totalComplex k B M` be the signed total of the canonical positive
proper-shuffle bicomplex. The map `ordinaryProperAugmentation k B M : T ⟶
ordinaryProperCotangentComplex k B M` is the inverse total-flip isomorphism, followed by the
augmented diagram's total augmentation and `(terminalProperCotangentIso k B M).hom`. -/
def ordinaryProperAugmentation : totalComplex k B M ⟶ ordinaryProperCotangentComplex k B M :=
  ((bicomplex k B M).totalFlipIso (.down ℕ)).inv ≫
    (augmentedChainTotalAugmentation (ModuleCat.{max u v w} k)).app (positiveProperDiagram k B M) ≫
      (terminalProperCotangentIso k B M).hom

/-- For a commutative `ℚ`-algebra `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive
group `M : Type w` with `Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower
k B M` with `Module.Flat k B`, the map `ordinaryProperAugmentation k B M` is a
quasi-isomorphism. It compares the signed polynomial-resolution proper-shuffle total with the
ordinary proper-shuffle complex restricted to positive degrees, using the flat-target
coefficient rows and their Eulerian arrow retract. -/
instance ordinaryProperAugmentation_quasiIso [Module.Flat k B] :
    _root_.QuasiIso (ordinaryProperAugmentation k B M) := by
  let a := ((bicomplex k B M).totalFlipIso (.down ℕ)).inv
  let b := (augmentedChainTotalAugmentation (ModuleCat.{max u v w} k)).app (positiveProperDiagram k B M)
  let c := (terminalProperCotangentIso k B M).hom
  let _ : IsIso c := (terminalProperCotangentIso k B M).isIso_hom
  have hc : _root_.QuasiIso c := _root_.quasiIso_of_isIso c
  have hb : _root_.QuasiIso b := positiveProperTotalAugmentation_quasiIso k B M
  have hbc : _root_.QuasiIso (b ≫ c) := _root_.quasiIso_comp b c (hφ := hb) (hφ' := hc)
  have ha : _root_.QuasiIso a := _root_.quasiIso_of_isIso a
  exact _root_.quasiIso_comp a (b ≫ c) (hφ := ha) (hφ' := hbc)

/-- For a commutative `ℚ`-algebra `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive group `M : Type w` with
`Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M`, the morphism
`canonicalCotangentComparison k B M : totalComplex k B M ⟶ (alternatingFaceMapComplex (ModuleCat.{max u v w} k)).obj
(cotangentDiagram k B M)`
is `totalMap k B M` followed by `(alternatingSingleTotalIso _ (cotangentDiagram k B M)).hom`. It maps the canonical
positive proper-shuffle total to the coefficient cotangent diagram's alternating-face complex. -/
def canonicalCotangentComparison : totalComplex k B M ⟶
    (alternatingFaceMapComplex (ModuleCat.{max u v w} k)).obj (cotangentDiagram k B M) :=
  totalMap k B M ≫ (alternatingSingleTotalIso (ModuleCat.{max u v w} k) (cotangentDiagram k B M)).hom

/-- For a commutative `ℚ`-algebra `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive
group `M : Type w` with `Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower
k B M`, `canonicalCotangentComparison k B M` is a quasi-isomorphism. Its source is the signed
total of the canonical positive proper-shuffle bicomplex, and its target is the
alternating-face complex of `cotangentDiagram k B M`; the polynomial-level cotangent
comparisons give the vertical quasi-isomorphism. -/
instance canonicalCotangentComparison_quasiIso : _root_.QuasiIso (canonicalCotangentComparison k B M) := by
  let a := totalMap k B M
  let b := (alternatingSingleTotalIso (ModuleCat.{max u v w} k) (cotangentDiagram k B M)).hom
  have ha : _root_.QuasiIso a := totalMap_quasiIso k B M
  let _ : IsIso b :=
    (alternatingSingleTotalIso (ModuleCat.{max u v w} k) (cotangentDiagram k B M)).isIso_hom
  have hb : _root_.QuasiIso b := _root_.quasiIso_of_isIso b
  exact _root_.quasiIso_comp a b (hφ := ha) (hφ' := hb)

/-- For a commutative `ℚ`-algebra `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive group `M : Type w` with
`Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M` with `Module.Flat k B` and `n : ℕ`, the
horizontal augmentation induces
`(totalComplex k B M).homology n ≅ (ordinaryProperCotangentComplex k B M).homology n`.
The forward morphism is degree-`n` homology of `ordinaryProperAugmentation k B M`. -/
def ordinaryProperAugmentationHomologyIso [Module.Flat k B] (n : ℕ) :
    (totalComplex k B M).homology n ≅ (ordinaryProperCotangentComplex k B M).homology n :=
  _root_.isoOfQuasiIsoAt (ordinaryProperAugmentation k B M) n

/-- For a commutative `ℚ`-algebra `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive group `M : Type w` with
`Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M` and `n : ℕ`, the vertical cotangent
comparison induces
`(totalComplex k B M).homology n ≅ ((alternatingFaceMapComplex (ModuleCat.{max u v w} k)).obj (cotangentDiagram k B
M)).homology n`.
Its forward map is homology of `canonicalCotangentComparison k B M`. -/
def canonicalCotangentComparisonHomologyIso (n : ℕ) :
    (totalComplex k B M).homology n ≅
      ((alternatingFaceMapComplex (ModuleCat.{max u v w} k)).obj (cotangentDiagram k B M)).homology n :=
  _root_.isoOfQuasiIsoAt (canonicalCotangentComparison k B M) n

/-- For a commutative `ℚ`-algebra `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive group `M : Type w` with
`Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M` with `Module.Flat k B` and `n : ℕ`, there
is an isomorphism
`(ordinaryProperCotangentComplex k B M).homology n ≅ (ModuleCat.restrictScalars (algebraMap k B)).obj
(CommAlgCat.andreQuillenHomology k B (ModuleCat.of B M) n)`.
It passes through the two homology comparisons from the canonical proper-shuffle total, followed by cotangent
normalization and restriction of scalars. -/
def ordinaryProperHarrisonAndreQuillenIso [Module.Flat k B] (n : ℕ) :
    (ordinaryProperCotangentComplex k B M).homology n ≅
      (ModuleCat.restrictScalars (algebraMap k B)).obj
        (CommAlgCat.andreQuillenHomology k B (ModuleCat.of B M) n) :=
  (ordinaryProperAugmentationHomologyIso k B M n).symm ≪≫
    canonicalCotangentComparisonHomologyIso k B M n ≪≫
    (canonicalCoefficientAlternatingHomologyIso k B M n).symm ≪≫
    canonicalGroundAndreQuillenHomologyIso k B M n

/-- For a commutative `ℚ`-algebra `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive group `M : Type w` with
`Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M` with `Module.Flat k B` and `n : ℕ`, the map
from `(ordinaryProperCotangentComplex k B M).homology n` to the underlying `k`-module of `andreQuillenHomology k B M n`
is
`(ordinaryProperAugmentationHomologyIso k B M n).inv ≫ (canonicalCotangentComparisonHomologyIso k B M n).hom ≫
(canonicalCoefficientAlternatingHomologyIso k B M n).inv ≫ (canonicalGroundAndreQuillenHomologyIso k B M n).hom`. -/
def ordinaryProperHarrisonAndreQuillenHomologyMap [Module.Flat k B] (n : ℕ) :
    (ordinaryProperCotangentComplex k B M).homology n ⟶
      (ModuleCat.restrictScalars (algebraMap k B)).obj
        (CommAlgCat.andreQuillenHomology k B (ModuleCat.of B M) n) :=
  (ordinaryProperAugmentationHomologyIso k B M n).inv ≫
    (canonicalCotangentComparisonHomologyIso k B M n).hom ≫
    (canonicalCoefficientAlternatingHomologyIso k B M n).inv ≫
    (canonicalGroundAndreQuillenHomologyIso k B M n).hom

/-- For a commutative `ℚ`-algebra `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive group `M : Type w` with
`Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M` with `Module.Flat k B` and `n : ℕ`,
`(ordinaryProperHarrisonAndreQuillenIso k B M n).hom = ordinaryProperHarrisonAndreQuillenHomologyMap k B M n`.
The isomorphism's forward morphism is therefore the composite of the horizontal inverse, vertical cotangent map,
normalization comparison, and ground-scalar homology comparison. -/
theorem ordinaryProperHarrisonAndreQuillenIso_hom [Module.Flat k B] (n : ℕ) :
    @Eq ((ordinaryProperCotangentComplex k B M).homology n ⟶
      (ModuleCat.restrictScalars (algebraMap k B)).obj
        (CommAlgCat.andreQuillenHomology k B (ModuleCat.of B M) n))
      (ordinaryProperHarrisonAndreQuillenIso k B M n).hom
      (ordinaryProperHarrisonAndreQuillenHomologyMap k B M n) := rfl

omit [Algebra ℚ k] [SMulCommClass k B M] in
/-- Let `k : Type u` be a commutative ring, `B : CommAlgCat.{max u v} k`, and `M : Type w` an additive group with
`Module k M`, `Module B M`, and `IsScalarTower k B M`. Then
`(positiveQuotient k B M).d 1 0 = 0`.
The degree-one boundary vanishes for the symmetric coefficient action and descends through the surjective proper-shuffle
projection. -/
theorem ordinaryProperBoundary_one_zero : (positiveQuotient k B M).d 1 0 = 0 := by
  let π := properShuffleProjection k B M
  let _ : Epi (π.f 1) := (ModuleCat.epi_iff_surjective _).mpr
    ((rawPositiveRelations k B M 1).mkQ_surjective)
  apply (cancel_epi (π.f 1)).mp
  exact (π.comm 1 0).symm.trans
    ((congrArg (fun d => d ≫ π.f 0) (boundary_one_zero k B M)).trans
      (Limits.zero_comp.trans Limits.comp_zero.symm))

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive coefficient `M : Type w` with
compatible `k`- and `B`-module actions, every `n : ℕ` has an isomorphism
`(ordinaryProperCotangentComplex k B M).homology n ≅ (positiveQuotient k B M).homology (n+1)`.
The degree-one boundary of the quotient is zero, so the positive restriction also gives this comparison at `n=0`. -/
def ordinaryProperRestrictionHomologyIso (n : ℕ) :
    (ordinaryProperCotangentComplex k B M).homology n ≅ (positiveQuotient k B M).homology (n + 1) :=
  ChainComplex.positiveRestrictionHomologyIso (positiveQuotient k B M)
    (ordinaryProperBoundary_one_zero k B M) n

/-- For a commutative `ℚ`-algebra `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive group `M : Type w` with
`Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M` with `Module.Flat k B` and `n : ℕ`,
`(positiveQuotient k B M).homology (n+1) ≅ (ModuleCat.restrictScalars (algebraMap k B)).obj
(CommAlgCat.andreQuillenHomology k B (ModuleCat.of B M) n)`.
This composes the inverse positive-restriction homology isomorphism with the canonical restricted proper
Harrison–André–Quillen comparison. -/
def ordinaryProperHarrisonPositiveAndreQuillenIso [Module.Flat k B] (n : ℕ) :
    (positiveQuotient k B M).homology (n + 1) ≅
      (ModuleCat.restrictScalars (algebraMap k B)).obj
        (CommAlgCat.andreQuillenHomology k B (ModuleCat.of B M) n) :=
  (ordinaryProperRestrictionHomologyIso k B M n).symm ≪≫
    ordinaryProperHarrisonAndreQuillenIso k B M n

/-- For a commutative `ℚ`-algebra `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive group `M : Type w` with
`Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M` with `Module.Flat k B`, let `n : ℕ` satisfy
`1 ≤ n`. Then
`(positiveQuotient k B M).homology n ≅ (ModuleCat.restrictScalars (algebraMap k B)).obj (CommAlgCat.andreQuillenHomology
k B (ModuleCat.of B M) (n−1))`.
Thus every positive proper Harrison degree `n` is identified with canonical André–Quillen degree `n−1` for the same
coefficient module. -/
def ordinaryProperHarrisonAndreQuillenIso_at [Module.Flat k B] (n : ℕ) (hn : 1 ≤ n) :
    (positiveQuotient k B M).homology n ≅
      (ModuleCat.restrictScalars (algebraMap k B)).obj
        (CommAlgCat.andreQuillenHomology k B (ModuleCat.of B M) (n - 1)) := by
  have h : n - 1 + 1 = n := Nat.sub_add_cancel hn
  exact (eqToIso (congrArg (fun j => (positiveQuotient k B M).homology j) h.symm)) ≪≫
      ordinaryProperHarrisonPositiveAndreQuillenIso k B M (n - 1)

end ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle.Canonical
