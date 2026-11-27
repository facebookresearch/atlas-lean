/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.Hochschild.CanonicalCoefficientHochschildAugmentation
public import MathlibExt.Algebra.Homology.Hochschild.ProperShuffleAugmentedRetract

/-!
# Positive Hochschild and proper-shuffle augmentations

Let `k : Type u` be a commutative ring, `B : CommAlgCat.{max u v} k`, and `M : Type w` an
additive group with compatible `k`- and `B`-module actions. The positive Hochschild diagram of
the canonical polynomial resolution has degree `q` equal to Hochschild degree `q+1`. Its
horizontal augmentation therefore uses the arbitrary-coefficient tensor-power augmentation in
degree `q+1`.

If `B` is flat over `k`, every positive horizontal row and the positive Hochschild total
augmentation are quasi-isomorphisms. When `k` also has an `ℚ`-algebra structure, the Eulerian
retract transfers this comparison to the proper-shuffle quotient, whose relations use two
strictly positive shuffle factors. The resulting total homology is isomorphic to the homology
of the augmented terminal proper quotient.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite
open scoped TensorProduct Simplicial

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle.Canonical

open AugmentedAlgebra

variable (k : Type u) [CommRing k] [Algebra ℚ k] (B : CommAlgCat.{max u v} k)
  (M : Type w) [AddCommGroup M] [Module k M] [Module B M]
  [SMulCommClass k B M] [IsScalarTower k B M]

/-- For a commutative ring `k : Type u` and `B : CommAlgCat.{max u v} k`,
`canonicalAlgebraResolution k B` is `AugmentedCoefficients.Canonical.resolution k B`, the
canonical simplicial polynomial resolution augmented to `B`. -/
abbrev canonicalAlgebraResolution :=
  AugmentedCoefficients.Canonical.resolution k B

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive group `M :
Type w` with `Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M`,
`positiveHochschildDiagram k B M` is the augmented simplicial chain diagram
`positiveHochschildAugmented k B M (canonicalAlgebraResolution k B)`. At a
polynomial-resolution level `P_p`, its degree `q` represents `M ⊗_k P_p^{⊗ (q+1)}`; its
augmentation goes to the positive Hochschild complex of `B` with coefficient `M`. -/
abbrev positiveHochschildDiagram :=
  positiveHochschildAugmented k B M (canonicalAlgebraResolution k B)

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive group `M :
Type w` with `Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M`,
`positiveProperDiagram k B M` is `positiveQuotientAugmented k B M (canonicalAlgebraResolution
k B)`. It applies the positive proper-shuffle quotient in every polynomial-resolution degree
and augments to its value at `B ⟶ B`. The relations are signed shuffle products whose two
input degrees are strictly positive. -/
abbrev positiveProperDiagram :=
  positiveQuotientAugmented k B M (canonicalAlgebraResolution k B)

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive group `M :
Type w` with `Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M`, the
bicomplex `positiveHochschildBicomplex k B M` has both shapes `.down ℕ` and values in
`ModuleCat.{max u v w} k`. It is the alternating-face complex of `(positiveHochschildDiagram k
B M).left`; its `(p,q)` term corresponds to Hochschild degree `q+1` at polynomial-resolution
level `p`. -/
abbrev positiveHochschildBicomplex :
    HomologicalComplex₂ (ModuleCat.{max u v w} k) (.down ℕ) (.down ℕ) :=
  (alternatingFaceMapComplex (ChainComplex (ModuleCat.{max u v w} k) ℕ)).obj
    (positiveHochschildDiagram k B M).left

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive group `M : Type w` with `Module k
M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M` and `q : ℕ`, there is an isomorphism
`(positiveHochschildBicomplex k B M).flip.X q ≅ (AugmentedCoefficients.Canonical.bicomplex k B M).flip.X (q+1)`.
Evaluation and the alternating-face construction identify the positive row at `q` with the ordinary Hochschild row at
`q+1`. -/
def positiveRowSourceIso (q : ℕ) :
    (positiveHochschildBicomplex k B M).flip.X q ≅
      (AugmentedCoefficients.Canonical.bicomplex k B M).flip.X (q + 1) :=
  (alternatingFaceMapComplexCompMapHomologicalComplexIso
    (HomologicalComplex.eval (ModuleCat.{max u v w} k) (.down ℕ) q)).app
      (positiveHochschildDiagram k B M).left ≪≫
    ((alternatingFaceMapComplexCompMapHomologicalComplexIso
      (HomologicalComplex.eval (ModuleCat.{max u v w} k) (.down ℕ) (q + 1))).app
        (AugmentedCoefficients.Canonical.diagram k B M)).symm

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive group `M : Type w` with `Module k
M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M` and `q : ℕ`,
`(AugmentedCoefficients.terminalComplex k B M).X (q+1) ≅ (positiveHochschildDiagram k B M).right.X q`.
Both are the coefficient Hochschild term `M ⊗_k B^{⊗ (q+1)}` represented in universe `max u v w`. -/
def positiveRowTargetIso (q : ℕ) :
    (AugmentedCoefficients.terminalComplex k B M).X (q + 1) ≅
      (positiveHochschildDiagram k B M).right.X q := Iso.refl _

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive group `M : Type w` with `Module k
M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M` and `q : ℕ`, the map from
`(positiveHochschildBicomplex k B M).flip.X q` to the terminal degree-`q` module concentrated at zero is
`(positiveRowSourceIso k B M q).hom ≫ AugmentedCoefficients.Canonical.horizontalAugmentationComponent k B M (q+1) ≫
(ChainComplex.single₀ _).map (positiveRowTargetIso k B M q).hom`.
It uses the ordinary coefficient-tensor row at Hochschild degree `q+1`. -/
def positiveHorizontalComponent (q : ℕ) :
    (positiveHochschildBicomplex k B M).flip.X q ⟶
      (ChainComplex.single₀ (ModuleCat.{max u v w} k)).obj
        ((positiveHochschildDiagram k B M).right.X q) :=
  (positiveRowSourceIso k B M q).hom ≫
    AugmentedCoefficients.Canonical.horizontalAugmentationComponent k B M (q + 1) ≫
      (ChainComplex.single₀ (ModuleCat.{max u v w} k)).map (positiveRowTargetIso k B M q).hom

/-- For a commutative `ℚ`-algebra `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive group `M : Type w` with
`Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M` and `q : ℕ`,
`positiveHorizontalComponent k B M q = augmentedChainHorizontalAugmentation (ModuleCat.{max u v w} k)
(positiveHochschildDiagram k B M) q`.
The row map obtained from the ordinary degree-`q+1` tensor augmentation is the horizontal augmentation of the augmented
positive chain diagram. -/
theorem positiveHorizontalComponent_eq (q : ℕ) :
    positiveHorizontalComponent k B M q =
      augmentedChainHorizontalAugmentation (ModuleCat.{max u v w} k)
        (positiveHochschildDiagram k B M) q := by
  apply HomologicalComplex.to_single_hom_ext (j := 0)
  let a := positiveRowSourceIso k B M q
  let b := AugmentedCoefficients.Canonical.horizontalAugmentationComponent k B M (q + 1)
  let c := (ChainComplex.single₀ (ModuleCat.{max u v w} k)).map (positiveRowTargetIso k B M q).hom
  have ha : a.hom.f 0 = 𝟙 (((AugmentedCoefficients.Canonical.bicomplex k B M).X 0).X (q + 1)) := rfl
  have hb : b.f 0 = ((AugmentedCoefficients.Canonical.diagramAugmentation k B M).app (op ⦋0⦌)).f (q + 1) :=
    AugmentedCoefficients.Canonical.horizontalAugmentationComponent_f_zero k B M (q + 1)
  have hc : c.f 0 = 𝟙 ((positiveHochschildDiagram k B M).right.X q) := rfl
  have hd : (augmentedChainHorizontalAugmentation (ModuleCat.{max u v w} k)
      (positiveHochschildDiagram k B M) q).f 0 =
        ((AugmentedCoefficients.Canonical.diagramAugmentation k B M).app (op ⦋0⦌)).f (q + 1) :=
    augmentedChainHorizontalAugmentation_f_zero (ModuleCat.{max u v w} k)
      (positiveHochschildDiagram k B M) q
  change (a.hom ≫ b ≫ c).f 0 = _
  exact (HomologicalComplex.comp_f a.hom (b ≫ c) 0).trans
    ((congrArg₂ (fun x y => x ≫ y) ha (HomologicalComplex.comp_f b c 0)).trans
      ((congrArg (fun t => 𝟙 _ ≫ t) (congrArg₂ (fun x y => x ≫ y) hb hc)).trans
        ((Category.id_comp _).trans ((Category.comp_id _).trans hd.symm))))

omit [Algebra ℚ k] in
/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive group `M :
Type w` with `Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M`,
assume `Module.Flat k B`. Then every `q : ℕ` satisfies `QuasiIso (positiveHorizontalComponent
k B M q)`. The source is the alternating polynomial row in positive Hochschild degree `q`, and
the target is `M ⊗_k B^{⊗ (q+1)}` concentrated at zero. Flatness is imposed on `B`. -/
theorem positiveHorizontalComponent_quasiIso [Module.Flat k B] (q : ℕ) :
    _root_.QuasiIso (positiveHorizontalComponent k B M q) := by
  let _ : _root_.QuasiIso
      (AugmentedCoefficients.Canonical.horizontalAugmentationComponent k B M (q + 1)) :=
    AugmentedCoefficients.Canonical.horizontalAugmentationComponent_quasiIso k B M (q + 1)
  unfold positiveHorizontalComponent
  infer_instance

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive group `M : Type w` with `Module k
M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M` with `Module.Flat k B`, the map
`(augmentedChainTotalAugmentation (ModuleCat.{max u v w} k)).app (positiveHochschildDiagram k B M)`
is a quasi-isomorphism. It augments the signed total of the canonical positive Hochschild diagram to its terminal
positive Hochschild complex with coefficient `M`. -/
instance positiveHochschildTotalAugmentation_quasiIso [Module.Flat k B] :
    _root_.QuasiIso ((augmentedChainTotalAugmentation (ModuleCat.{max u v w} k)).app
      (positiveHochschildDiagram k B M)) := by
  let f := (augmentedChainBicomplexAugmentation (ModuleCat.{max u v w} k)).app
    (positiveHochschildDiagram k B M)
  have hf : ∀ q : ℕ, _root_.QuasiIso (f.f q) := by
    intro q
    change _root_.QuasiIso (augmentedChainHorizontalAugmentation (ModuleCat.{max u v w} k)
      (positiveHochschildDiagram k B M) q)
    rw [← positiveHorizontalComponent_eq]
    exact positiveHorizontalComponent_quasiIso k B M q
  let _ : _root_.QuasiIso (HomologicalComplex₂.total.map f (.down ℕ)) :=
    HomologicalComplex₂.quasiIso_totalMap_of_objwise_firstQuadrant f hf
  change _root_.QuasiIso (HomologicalComplex₂.totalAugmentationDownNat f)
  unfold HomologicalComplex₂.totalAugmentationDownNat
  infer_instance

/-- For a commutative `ℚ`-algebra `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive group `M : Type w` with
`Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M` with `Module.Flat k B`, the map
`(augmentedChainTotalAugmentation (ModuleCat.{max u v w} k)).app (positiveProperDiagram k B M)`
is a quasi-isomorphism. The Eulerian arrow retract of the positive Hochschild augmentation transfers its
quasi-isomorphism property to the quotient by shuffles with two strictly positive input degrees. -/
instance positiveProperTotalAugmentation_quasiIso [Module.Flat k B] :
    _root_.QuasiIso ((augmentedChainTotalAugmentation (ModuleCat.{max u v w} k)).app
      (positiveProperDiagram k B M)) :=
  _root_.quasiIso_of_retractArrow
    (positiveTotalAugmentationRetract k B M (canonicalAlgebraResolution k B))

/-- For a commutative `ℚ`-algebra `k : Type u`, `B : CommAlgCat.{max u v} k`, and an additive group `M : Type w` with
`Module k M`, `Module B M`, `SMulCommClass k B M`, and `IsScalarTower k B M` with `Module.Flat k B` and `n : ℕ`, the
total augmentation induces an isomorphism
`((augmentedChainTotalFunctor (ModuleCat.{max u v w} k)).obj (positiveProperDiagram k B M)).homology n ≅
(positiveProperDiagram k B M).right.homology n`.
Its forward map is the degree-`n` homology map of that augmentation. -/
def positiveProperTotalHomologyIso [Module.Flat k B] (n : ℕ) :
    ((augmentedChainTotalFunctor (ModuleCat.{max u v w} k)).obj
      (positiveProperDiagram k B M)).homology n ≅
        (positiveProperDiagram k B M).right.homology n :=
  _root_.isoOfQuasiIsoAt
    ((augmentedChainTotalAugmentation (ModuleCat.{max u v w} k)).app
      (positiveProperDiagram k B M)) n

end ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle.Canonical
