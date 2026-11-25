/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Monad.CartesianClassifyingBarNaturality
public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-!
# Topological classifying and universal bars

This file specializes the landed categorical classifying-bar construction to a
topological monoid, internally in the cartesian monoidal category `TopCat`.
The simplicial objects here are genuinely `TopCat`-valued; no passage through
the underlying type-valued classifying nerve is used.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite

namespace CategoryTheory
namespace Monad

universe u

variable (G : Type u) [TopologicalSpace G] [Monoid G] [ContinuousMul G]

/-- A topological monoid as an object of `TopCat`. -/
@[reducible]
def GTop : TopCat.{u} :=
  TopCat.of G

/-- The continuous unit map of a topological monoid object. -/
noncomputable def GTopOne : 𝟙_ (TopCat.{u}) ⟶ GTop G :=
  TopCat.ofHom ⟨fun _ => 1, continuous_const⟩

/-- The continuous multiplication map of a topological monoid object. -/
noncomputable def GTopMul : GTop G ⊗ GTop G ⟶ GTop G :=
  TopCat.ofHom ⟨fun p => p.1 * p.2, continuous_mul⟩

/-- The internal monoid object carried by a topological monoid. -/
@[instance_reducible]
noncomputable def GTopMonObj : MonObj (GTop G) where
  one := GTopOne G
  mul := GTopMul G
  one_mul := by
    apply TopCat.hom_ext
    ext p
    change 1 * p.2 = p.2
    exact one_mul _
  mul_one := by
    apply TopCat.hom_ext
    ext p
    change p.1 * 1 = p.1
    exact mul_one _
  mul_assoc := by
    apply TopCat.hom_ext
    ext p
    change (p.1.1 * p.1.2) * p.2 = p.1.1 * (p.1.2 * p.2)
    exact mul_assoc _ _ _

attribute [local instance] GTopMonObj

/-- The bundled internal topological monoid. -/
noncomputable abbrev GTopMon : Mon TopCat.{u} where
  X := GTop G

@[simp]
theorem GTopMon_X : (GTopMon G).X = GTop G :=
  rfl

/-- The canonical point object in `TopCat`. -/
@[reducible]
def topPoint : TopCat.{u} :=
  𝟙_ (TopCat.{u})

/-- The trivial left action of a topological monoid on the point. -/
@[instance_reducible]
noncomputable def topPointModObj : ModObj (GTop G) topPoint.{u} :=
  ClassifyingBar.pointModObj (GTopMon G)

attribute [local instance] topPointModObj

/-- The terminal right action on the point. -/
noncomputable def topPointRightAction : topPoint.{u} ⊗ GTop G ⟶ topPoint.{u} :=
  CartesianMonoidalCategory.fst topPoint.{u} (GTop G)

/-- Unit law for the terminal right action. -/
theorem topPointRightAction_one :
    (topPoint.{u} ◁ MonObj.one (X := GTop G)) ≫ topPointRightAction G =
      (ρ_ topPoint.{u}).hom :=
  ClassifyingBar.pointRightAction_one (GTopMon G)

/-- Associativity law for the terminal right action. -/
theorem topPointRightAction_assoc :
    (α_ topPoint.{u} (GTop G) (GTop G)).hom ≫
        (topPoint.{u} ◁ MonObj.mul (X := GTop G)) ≫ topPointRightAction G =
      (topPointRightAction G ▷ GTop G) ≫ topPointRightAction G :=
  ClassifyingBar.pointRightAction_assoc (GTopMon G)

/-- The terminal augmentation from the monoid to the point. -/
noncomputable def topAugmentation : GTop G ⟶ topPoint.{u} :=
  CartesianMonoidalCategory.toUnit (GTop G)

/-- Compatibility of the terminal augmentation with the two right actions. -/
theorem topAugmentation_compat :
    (topAugmentation G ▷ GTop G) ≫ topPointRightAction G =
      MonObj.mul (X := GTop G) ≫ topAugmentation G :=
  ClassifyingBar.augmentation_compat (GTopMon G)

/-- The canonical point of the discrete indexing category. -/
def topBarIndex : Discrete PUnit.{1} :=
  ClassifyingBar.index

/-- Evaluation of a point-indexed `TopCat` diagram at its canonical point. -/
noncomputable def topBarEvaluation :
    (Discrete PUnit.{1} ⥤ TopCat.{u}) ⥤ TopCat.{u} :=
  ClassifyingBar.pointEvaluation TopCat.{u}

/-- The genuine topological classifying bar `B(*, G, *)`. -/
noncomputable def BBar : SimplicialObject TopCat.{u} :=
  (ClassifyingBar.classifyingBarFunctor TopCat.{u}).obj (GTopMon G)

/-- The genuine topological universal bar `B(G, G, *)`. -/
noncomputable def EBar : SimplicialObject TopCat.{u} :=
  (ClassifyingBar.universalBarFunctor TopCat.{u}).obj (GTopMon G)

/-- The evaluated universal-bundle map `EBar G ⟶ BBar G`. -/
noncomputable def EBarToBBar : EBar G ⟶ BBar G :=
  (ClassifyingBar.universalBundleNatTrans TopCat.{u}).app (GTopMon G)

/-- The regular augmented universal bar, evaluated at the canonical point. -/
noncomputable def EBarAugmented : SimplicialObject.Augmented TopCat.{u} :=
  ClassifyingBar.universalBarAugmented (GTopMon G)

/-- The simplicial object underlying the evaluated augmentation is `EBar`. -/
@[simp]
theorem EBarAugmented_left :
    (EBarAugmented G).left = EBar G :=
  ClassifyingBar.universalBarAugmented_left (GTopMon G)

/-- The target of the evaluated augmentation is the canonical point. -/
@[simp]
theorem EBarAugmented_right :
    (EBarAugmented G).right = topPoint.{u} :=
  ClassifyingBar.universalBarAugmented_right (GTopMon G)

/-- The evaluated genuine extra degeneracy on the universal bar. -/
noncomputable def EBarExtraDegeneracy :
    SimplicialObject.Augmented.ExtraDegeneracy (EBarAugmented G) :=
  (BarRegularContraction.extraDegeneracySimplicial
    (leftPointModule (GTop G) topPoint.{u})).map topBarEvaluation

/-- The augmentation section is evaluation of the regular section. -/
@[simp]
theorem EBarExtraDegeneracy_s' :
    (EBarExtraDegeneracy G).s' =
      (BarRegularContraction.s'
        (leftPointModule (GTop G) topPoint.{u})).app topBarIndex :=
  rfl

/-- Each extra degeneracy is evaluation of the regular operator. -/
@[simp]
theorem EBarExtraDegeneracy_s (n : ℕ) :
    (EBarExtraDegeneracy G).s n =
      (BarRegularContraction.s
        (leftPointModule (GTop G) topPoint.{u}) n).app topBarIndex :=
  rfl

/-- The evaluated universal-bar augmentation is split epi. -/
noncomputable def EBarSplitEpi : SplitEpi (EBarAugmented G).hom :=
  (EBarExtraDegeneracy G).splitEpi

/-- The standard contraction homotopy of the evaluated universal bar. -/
noncomputable def EBarHomotopy :
    SimplicialObject.Homotopy
      ((EBarAugmented G).hom ≫ (EBarExtraDegeneracy G).section_)
      (𝟙 (EBarAugmented G).left) :=
  (EBarExtraDegeneracy G).homotopy

section Functoriality

variable {H : Type u} [TopologicalSpace H] [Monoid H] [ContinuousMul H]

/-- The `TopCat` morphism underlying a continuous monoid homomorphism. -/
noncomputable def GTopMap (phi : ContinuousMonoidHom G H) : GTop G ⟶ GTop H :=
  TopCat.ofHom phi.toContinuousMap

/-- A continuous monoid homomorphism is an internal monoid morphism in `TopCat`. -/
noncomputable instance GTopMap_isMonHom (phi : ContinuousMonoidHom G H) :
    IsMonHom (GTopMap G phi) where
  one_hom := by
    apply TopCat.hom_ext
    ext p
    change phi 1 = 1
    exact map_one phi
  mul_hom := by
    apply TopCat.hom_ext
    ext p
    change phi (p.1 * p.2) = phi p.1 * phi p.2
    exact map_mul phi _ _

/-- A continuous monoid homomorphism as a morphism of bundled internal topological monoids. -/
noncomputable def GTopMonMap (phi : ContinuousMonoidHom G H) :
    GTopMon G ⟶ GTopMon H :=
  Mon.ofHom (GTopMap G phi)

@[simp]
theorem GTopMonMap_hom (phi : ContinuousMonoidHom G H) :
    (GTopMonMap G phi).hom = GTopMap G phi :=
  rfl

@[simp]
theorem GTopMonMap_id :
    GTopMonMap G (ContinuousMonoidHom.id G) = 𝟙 (GTopMon G) := by
  apply Mon.Hom.ext'
  apply TopCat.hom_ext
  ext x
  rfl

@[simp]
theorem GTopMonMap_comp
    {K : Type u} [TopologicalSpace K] [Monoid K] [ContinuousMul K]
    (phi : ContinuousMonoidHom G H) (psi : ContinuousMonoidHom H K) :
    GTopMonMap G phi ≫ GTopMonMap H psi =
      GTopMonMap G (psi.comp phi) := by
  apply Mon.Hom.ext'
  apply TopCat.hom_ext
  ext x
  rfl

/-- Tensor-monad morphism induced by a continuous monoid homomorphism. -/
noncomputable def topTensorMonadHom (phi : ContinuousMonoidHom G H) :
    tensorMonad (GTop G) ⟶ tensorMonad (GTop H) :=
  tensorMonadHom (GTopMonMap G phi)

/-- Pointwise formula for the induced tensor-monad morphism. -/
@[simp]
theorem topTensorMonadHom_app (phi : ContinuousMonoidHom G H)
    (X : TopCat.{u}) (p : G × X) :
    (topTensorMonadHom G phi).app X p = (phi p.1, p.2) :=
  rfl

/-- The identity continuous homomorphism induces the identity tensor-monad morphism. -/
@[simp]
theorem topTensorMonadHom_id :
    topTensorMonadHom G (ContinuousMonoidHom.id G) = 𝟙 _ := by
  unfold topTensorMonadHom
  rw [GTopMonMap_id, tensorMonadHom_id]

/-- Tensor-monad morphisms compose with continuous monoid homomorphisms. -/
@[simp]
theorem topTensorMonadHom_comp
    {K : Type u} [TopologicalSpace K] [Monoid K] [ContinuousMul K]
    (phi : ContinuousMonoidHom G H) (psi : ContinuousMonoidHom H K) :
    topTensorMonadHom G (psi.comp phi) =
      topTensorMonadHom G phi ≫ topTensorMonadHom H psi := by
  unfold topTensorMonadHom
  rw [← GTopMonMap_comp, tensorMonadHom_comp]

/-- Classifying-bar map induced by a continuous monoid homomorphism. -/
noncomputable def BBarMap (phi : ContinuousMonoidHom G H) : BBar G ⟶ BBar H :=
  (ClassifyingBar.classifyingBarFunctor TopCat.{u}).map (GTopMonMap G phi)

/-- Degreewise tensor-power formula for the induced classifying-bar map. -/
theorem BBarMap_app_op_mk (phi : ContinuousMonoidHom G H) (n : ℕ) :
    (BBarMap G phi).app (op (SimplexCategory.mk n)) =
      (tensorLeft topPoint.{u}).map
        ((monadPowHom (topTensorMonadHom G phi) n).app topPoint.{u}) :=
  ClassifyingBar.classifyingBarMap_app_op_mk (GTopMonMap G phi) n

/-- The identity continuous homomorphism induces the identity classifying-bar map. -/
theorem BBarMap_id :
    BBarMap G (ContinuousMonoidHom.id G) = 𝟙 (BBar G) := by
  unfold BBarMap BBar
  rw [GTopMonMap_id, Functor.map_id]

/-- Classifying-bar maps compose with continuous monoid homomorphisms. -/
theorem BBarMap_comp
    {K : Type u} [TopologicalSpace K] [Monoid K] [ContinuousMul K]
    (phi : ContinuousMonoidHom G H) (psi : ContinuousMonoidHom H K) :
    BBarMap G phi ≫ BBarMap H psi = BBarMap G (psi.comp phi) := by
  unfold BBarMap BBar
  rw [← Functor.map_comp, GTopMonMap_comp]

/-- The monad hom as a morphism from the regular source module to the
restricted regular target module. -/
noncomputable def topRegularRightModuleHom (phi : ContinuousMonoidHom G H) :
    RightModule.regular (tensorMonad (GTop G)) ⟶
      (rightModuleRestrictAlongHom (topTensorMonadHom G phi)).obj
        (RightModule.regular (tensorMonad (GTop H))) :=
  tensorMonadRegularRightModuleHom (GTopMonMap G phi)

/-- Identity on the point as a morphism to the point module restricted along
the induced monad hom. -/
noncomputable def topPointRestrictedModuleHom (phi : ContinuousMonoidHom G H) :
    leftPointModule (GTop G) topPoint.{u} ⟶
      (leftModuleRestrictAlongHom (topTensorMonadHom G phi)).obj
        (leftPointModule (GTop H) topPoint.{u}) where
  f := 𝟙 _
  h := by
    apply NatTrans.ext
    funext a
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    change (PUnit.unit : PUnit.{u + 1}) = PUnit.unit
    rfl

/-- Universal-bar map induced by a continuous monoid homomorphism.

It first maps the regular and point modules into their restrictions along the
tensor-monad hom, then applies the generic monad-change map. -/
noncomputable def EBarMap (phi : ContinuousMonoidHom G H) : EBar G ⟶ EBar H :=
  (ClassifyingBar.universalBarFunctor TopCat.{u}).map (GTopMonMap G phi)

/-- Degreewise tensor-power formula for the induced universal-bar map. -/
theorem EBarMap_app_op_mk (phi : ContinuousMonoidHom G H) (n : ℕ) :
    (EBarMap G phi).app (op (SimplexCategory.mk n)) =
      (topTensorMonadHom G phi).app
          ((monadPow (tensorMonad (GTop G)) n).obj topPoint.{u}) ≫
        (tensorMonad (GTop H)).map
          ((monadPowHom (topTensorMonadHom G phi) n).app topPoint.{u}) :=
  ClassifyingBar.universalBarMap_app_op_mk (GTopMonMap G phi) n

/-- The identity continuous homomorphism induces the identity universal-bar map. -/
theorem EBarMap_id :
    EBarMap G (ContinuousMonoidHom.id G) = 𝟙 (EBar G) := by
  unfold EBarMap EBar
  rw [GTopMonMap_id, Functor.map_id]

/-- Universal-bar maps compose with continuous monoid homomorphisms. -/
theorem EBarMap_comp
    {K : Type u} [TopologicalSpace K] [Monoid K] [ContinuousMul K]
    (phi : ContinuousMonoidHom G H) (psi : ContinuousMonoidHom H K) :
    EBarMap G phi ≫ EBarMap H psi = EBarMap G (psi.comp phi) := by
  unfold EBarMap EBar
  rw [← Functor.map_comp, GTopMonMap_comp]

/-- Naturality square for the topological universal-bundle map. -/
theorem EBarToBBar_naturality (phi : ContinuousMonoidHom G H) :
    EBarMap G phi ≫ EBarToBBar H = EBarToBBar G ≫ BBarMap G phi := by
  change ClassifyingBar.universalBarMap (GTopMonMap G phi) ≫
      ClassifyingBar.universalBundleMap (GTopMon H) =
    ClassifyingBar.universalBundleMap (GTopMon G) ≫
      ClassifyingBar.classifyingBarMap (GTopMonMap G phi)
  exact ClassifyingBar.universalBundle_naturality (GTopMonMap G phi)

/-- The universal-bar map as a morphism of the canonical augmented bars. -/
noncomputable def EBarAugmentedMap (phi : ContinuousMonoidHom G H) :
    EBarAugmented G ⟶ EBarAugmented H where
  left := EBarMap G phi
  right := 𝟙 topPoint.{u}
  w := by
    change ClassifyingBar.universalBarMap (GTopMonMap G phi) ≫
        ClassifyingBar.universalBarAugmentationMap (GTopMon H) =
      ClassifyingBar.universalBarAugmentationMap (GTopMon G) ≫
        (SimplicialObject.const TopCat.{u}).map (𝟙 topPoint.{u})
    rw [ClassifyingBar.universalBarAugmentation_naturality,
      Functor.map_id, Category.comp_id]

@[simp]
theorem EBarAugmentedMap_left (phi : ContinuousMonoidHom G H) :
    (EBarAugmentedMap G phi).left = EBarMap G phi :=
  rfl

@[simp]
theorem EBarAugmentedMap_right (phi : ContinuousMonoidHom G H) :
    (EBarAugmentedMap G phi).right = 𝟙 topPoint.{u} :=
  rfl

/-- Naturality of the canonical universal-bar augmentation. -/
theorem EBarAugmentation_naturality (phi : ContinuousMonoidHom G H) :
    EBarMap G phi ≫ (EBarAugmented H).hom =
      (EBarAugmented G).hom ≫
        (SimplicialObject.const TopCat.{u}).map (𝟙 topPoint.{u}) :=
  (EBarAugmentedMap G phi).w

end Functoriality

/-- Raw degree formula for the topological classifying bar. -/
@[simp]
theorem BBar_obj (n : ℕ) :
    (BBar G).obj (Opposite.op (SimplexCategory.mk n)) =
      (tensorLeft topPoint.{u}).obj
        ((monadPow (tensorMonad (GTop G)) n).obj topPoint.{u}) :=
  rfl

/-- Raw degree formula for the topological universal bar. -/
@[simp]
theorem EBar_obj (n : ℕ) :
    (EBar G).obj (Opposite.op (SimplexCategory.mk n)) =
      (tensorLeft (GTop G)).obj
        ((monadPow (tensorMonad (GTop G)) n).obj topPoint.{u}) :=
  rfl

/-- Append one final coordinate to a finite tuple, as a homeomorphism. -/
noncomputable def topFinSnocHomeomorph (n : ℕ) :
    ((Fin n → G) × G) ≃ₜ (Fin (n + 1) → G) :=
  ((Homeomorph.refl (Fin n → G)).prodCongr
      (Homeomorph.piUnique (fun _ : Fin 1 ↦ G)).symm).trans
    (Fin.appendHomeomorph (X := G) n 1)

/-- Prepend one head coordinate to a finite tuple, as a homeomorphism. -/
noncomputable def topFinConsHomeomorph (n : ℕ) :
    (G × (Fin n → G)) ≃ₜ (Fin (n + 1) → G) where
  toEquiv := Fin.consEquiv (fun _ : Fin (n + 1) ↦ G)
  continuous_toFun := continuous_pi fun i => Fin.cases continuous_fst
    (fun j => (continuous_apply j).comp continuous_snd) i
  continuous_invFun := (continuous_apply (0 : Fin (n + 1))).prodMk
    (continuous_pi fun i : Fin n => continuous_apply i.succ)

/-- Head-first tuple homeomorphism for powers of the topological tensor monad. -/
noncomputable def topMonadPowTupleHomeomorph (X : TopCat.{u}) :
    (n : ℕ) →
      ((monadPow (tensorMonad (GTop G)) n).obj X : Type _) ≃ₜ
        (Fin n → G) × X
  | 0 =>
      { toEquiv :=
          { toFun := fun x => (fun i => Fin.elim0 i, x)
            invFun := fun p => p.2
            left_inv := fun _ => rfl
            right_inv := fun p => by
              rcases p with ⟨f, x⟩
              apply Prod.ext
              · funext i
                exact Fin.elim0 i
              · rfl }
        continuous_toFun := continuous_const.prodMk continuous_id
        continuous_invFun := continuous_snd }
  | n + 1 =>
      (topMonadPowTupleHomeomorph ((tensorMonad (GTop G)).obj X) n).trans
        ((Homeomorph.prodAssoc (Fin n → G) G X).symm.trans
          ((topFinSnocHomeomorph (G := G) n).prodCongr (Homeomorph.refl X)))

/-- Degree-`n` topological classifying bar as the space of `n` head-first tuples. -/
noncomputable def BBarDegreeHomeomorph (n : ℕ) :
    ((BBar G).obj (Opposite.op (SimplexCategory.mk n)) : Type _) ≃ₜ
      (Fin n → G) :=
  (TopCat.homeoOfIso
      (λ_ ((monadPow (tensorMonad (GTop G)) n).obj topPoint.{u}))).trans
    ((topMonadPowTupleHomeomorph (G := G) topPoint.{u} n).trans
      (TopCat.homeoOfIso (ρ_ (TopCat.of (Fin n → G)))))

/-- Degree-`n` topological universal bar as the space of `n+1` head-first tuples. -/
noncomputable def EBarDegreeHomeomorph (n : ℕ) :
    ((EBar G).obj (Opposite.op (SimplexCategory.mk n)) : Type _) ≃ₜ
      (Fin (n + 1) → G) :=
  ((Homeomorph.refl G).prodCongr
      (topMonadPowTupleHomeomorph (G := G) topPoint.{u} n)).trans
    ((Homeomorph.prodAssoc G (Fin n → G) topPoint.{u}).symm.trans
      (((topFinConsHomeomorph (G := G) n).prodCongr
          (Homeomorph.refl topPoint.{u})).trans
        (TopCat.homeoOfIso (ρ_ (TopCat.of (Fin (n + 1) → G))))))

omit [Monoid G] [ContinuousMul G] in
/-- Evaluation of the finite-tuple snoc homeomorphism. -/
@[simp]
theorem topFinSnocHomeomorph_apply (n : ℕ) (t : Fin n → G) (g : G) :
    topFinSnocHomeomorph (G := G) n (t, g) = Fin.snoc t g := by
  change Fin.append t (fun _ => g) = Fin.snoc t g
  rw [Fin.append_right_eq_snoc]

omit [Monoid G] [ContinuousMul G] in
/-- Evaluation of the finite-tuple head-cons homeomorphism. -/
@[simp]
theorem topFinConsHomeomorph_apply (n : ℕ) (g : G) (t : Fin n → G) :
    topFinConsHomeomorph (G := G) n (g, t) = Fin.cons g t :=
  rfl

@[simp]
theorem topMonadPowTupleHomeomorph_zero_apply (X : TopCat.{u}) (x : X) :
    topMonadPowTupleHomeomorph (G := G) X 0 x = (fun i => Fin.elim0 i, x) :=
  rfl

/-- Successor computation: the new tensor-monad coordinate is appended to the
head-first tuple. -/
theorem topMonadPowTupleHomeomorph_succ_apply (X : TopCat.{u}) (n : ℕ)
    (x : ((monadPow (tensorMonad (GTop G)) (n + 1)).obj X : Type _)) :
    let p := topMonadPowTupleHomeomorph (G := G)
      ((tensorMonad (GTop G)).obj X) n x
    topMonadPowTupleHomeomorph (G := G) X (n + 1) x =
      (Fin.snoc p.1 p.2.1, p.2.2) := by
  change
    ((topFinSnocHomeomorph (G := G) n)
        ((topMonadPowTupleHomeomorph (G := G)
          ((tensorMonad (GTop G)).obj X) n x).1,
        (topMonadPowTupleHomeomorph (G := G)
          ((tensorMonad (GTop G)).obj X) n x).2.1),
      (topMonadPowTupleHomeomorph (G := G)
        ((tensorMonad (GTop G)).obj X) n x).2.2) = _
  rw [topFinSnocHomeomorph_apply]

omit [ContinuousMul G] in
@[simp]
theorem GTopOne_apply (p : (𝟙_ (TopCat.{u}) : Type _)) :
    GTopOne G p = 1 :=
  rfl

@[simp]
theorem GTopMul_apply (p : G × G) :
    GTopMul G p = p.1 * p.2 :=
  rfl

omit [Monoid G] [ContinuousMul G] in
@[simp]
theorem topPointRightAction_apply (p : (topPoint.{u} ⊗ GTop G : TopCat.{u})) :
    topPointRightAction G p = p.1 :=
  rfl

omit [Monoid G] [ContinuousMul G] in
@[simp]
theorem topAugmentation_apply (g : G) :
    topAugmentation G g = PUnit.unit :=
  rfl

/-- The generalized tuple homeomorphism is natural in the final object. -/
theorem topMonadPowTupleHomeomorph_map
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    ∀ (n : ℕ) (x : ((monadPow (tensorMonad (GTop G)) n).obj X : Type _)),
      topMonadPowTupleHomeomorph (G := G) Y n
          (((monadPow (tensorMonad (GTop G)) n).map f) x) =
        ((topMonadPowTupleHomeomorph (G := G) X n x).1,
          f (topMonadPowTupleHomeomorph (G := G) X n x).2) := by
  intro n
  induction n generalizing X Y with
  | zero =>
      intro x
      rfl
  | succ n ih =>
      intro x
      change topMonadPowTupleHomeomorph (G := G) Y (n + 1)
          (((monadPow (tensorMonad (GTop G)) n).map
            ((tensorMonad (GTop G)).map f)) x) = _
      rw [topMonadPowTupleHomeomorph_succ_apply,
        topMonadPowTupleHomeomorph_succ_apply]
      rw [ih ((tensorMonad (GTop G)).map f) x]
      rfl

@[simp]
theorem BBarDegreeHomeomorph_apply (n : ℕ)
    (x : ((BBar G).obj (Opposite.op (SimplexCategory.mk n)) : Type _)) :
    BBarDegreeHomeomorph G n x =
      (topMonadPowTupleHomeomorph (G := G) topPoint.{u} n x.2).1 :=
  rfl

@[simp]
theorem EBarDegreeHomeomorph_apply (n : ℕ)
    (x : ((EBar G).obj (Opposite.op (SimplexCategory.mk n)) : Type _)) :
    EBarDegreeHomeomorph G n x =
      Fin.cons x.1
        (topMonadPowTupleHomeomorph (G := G) topPoint.{u} n x.2).1 :=
  rfl

/-- Remove one coordinate from a head-first tuple. -/
def topTupleRemove {n : ℕ} (i : Fin (n + 1)) (t : Fin (n + 1) → G) :
    Fin n → G :=
  Fin.removeNth i t

/-- Multiply adjacent coordinates in a head-first tuple. -/
def topTupleContract {n : ℕ} (i : Fin n) (t : Fin (n + 1) → G) :
    Fin n → G :=
  Fin.contractNth i.castSucc (fun x y => x * y) t

/-- Insert the monoid unit in a head-first tuple. -/
def topTupleInsert {n : ℕ} (i : Fin (n + 1)) (t : Fin n → G) :
    Fin (n + 1) → G :=
  Fin.insertNth i 1 t

/-- Pointwise unit of the topological tensor monad. -/
@[simp]
theorem topTensorMonad_eta_apply (X : TopCat.{u}) (x : X) :
    (tensorMonad (GTop G)).η.app X x = (1, x) :=
  rfl

/-- Pointwise multiplication of the topological tensor monad. -/
@[simp]
theorem topTensorMonad_mu_apply (X : TopCat.{u})
    (p : G × G × X) :
    (tensorMonad (GTop G)).μ.app X p = (p.1 * p.2.1, p.2.2) :=
  rfl

omit [TopologicalSpace G] [ContinuousMul G] in
/-- Contracting below the final coordinate commutes with tuple snoc. -/
theorem topTupleContract_snoc (n : ℕ) (t : Fin (n + 1) → G) (g : G)
    (i : Fin n) :
    topTupleContract G i.castSucc (Fin.snoc t g) =
      Fin.snoc (topTupleContract G i t) g := by
  funext j
  cases j using Fin.lastCases with
  | last =>
      have hlt : ((i.castSucc.castSucc : Fin (n + 2)) : ℕ) <
          ((Fin.last n : Fin (n + 1)) : ℕ) := by
        simp only [Fin.val_castSucc, Fin.val_last]
        have := i.isLt
        omega
      have hL : topTupleContract G i.castSucc (Fin.snoc t g) (Fin.last n) =
          (Fin.snoc (α := fun _ => G) t g) (Fin.last n).succ := by
        exact Fin.contractNth_apply_of_gt _ _ _ _ hlt
      have e : (Fin.last n).succ = Fin.last (n + 1) := rfl
      rw [hL, e, Fin.snoc_last, Fin.snoc_last]
  | cast j =>
      by_cases h₁ : j.val < i.val <;> by_cases h₂ : j.val = i.val
      · exact absurd h₂ (ne_of_lt h₁)
      · have h₁c : ((Fin.castSucc j : Fin (n + 1)) : ℕ) <
            ((i.castSucc.castSucc : Fin (n + 2)) : ℕ) := by
          change j.val < i.val
          exact h₁
        have hL : topTupleContract G i.castSucc (Fin.snoc t g)
            (Fin.castSucc j) =
            (Fin.snoc (α := fun _ => G) t g) (Fin.castSucc (Fin.castSucc j)) :=
          Fin.contractNth_apply_of_lt _ _ _ _ h₁c
        have hR : topTupleContract G i t j = t j.castSucc :=
          Fin.contractNth_apply_of_lt _ _ _ _ h₁
        rw [Fin.snoc_castSucc, hL, hR, Fin.snoc_castSucc]
      · have hj : i = j := (Fin.ext h₂).symm
        subst hj
        have hE : ((Fin.castSucc i : Fin (n + 1)) : ℕ) =
            ((i.castSucc.castSucc : Fin (n + 2)) : ℕ) := rfl
        have hL : topTupleContract G i.castSucc (Fin.snoc t g)
            (Fin.castSucc i) =
            (Fin.snoc (α := fun _ => G) t g) (Fin.castSucc (Fin.castSucc i)) *
              (Fin.snoc (α := fun _ => G) t g) (Fin.castSucc i).succ :=
          Fin.contractNth_apply_of_eq _ _ _ _ hE
        have hR : topTupleContract G i t i = t i.castSucc * t i.succ :=
          Fin.contractNth_apply_of_eq _ _ _ _ rfl
        rw [Fin.snoc_castSucc, hL, hR, Fin.snoc_castSucc,
          ← Fin.castSucc_succ, Fin.snoc_castSucc]
      · have hgt₁ : ((i.castSucc.castSucc : Fin (n + 2)) : ℕ) <
            ((Fin.castSucc j : Fin (n + 1)) : ℕ) := by
          simp only [Fin.val_castSucc]
          omega
        have hL : topTupleContract G i.castSucc (Fin.snoc t g)
            (Fin.castSucc j) =
            (Fin.snoc (α := fun _ => G) t g) (Fin.castSucc j).succ :=
          Fin.contractNth_apply_of_gt _ _ _ _ hgt₁
        have hgt : i.val < j.val := by omega
        have hR : topTupleContract G i t j = t j.succ :=
          Fin.contractNth_apply_of_gt _ _ _ _ hgt
        have hj : j.castSucc.succ = j.succ.castSucc := by
          apply Fin.ext
          rfl
        rw [hL, hj, Fin.snoc_castSucc, Fin.snoc_castSucc, hR]

omit [TopologicalSpace G] [ContinuousMul G] in
/-- Contracting after a fixed head coordinate commutes with tuple cons. -/
theorem topTupleContract_cons (n : ℕ) (t : Fin (n + 1) → G) (g : G)
    (i : Fin n) :
    topTupleContract G i.succ (Fin.cons (α := fun _ => G) g t) =
      Fin.cons (α := fun _ => G) g (topTupleContract G i t) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · change Fin.contractNth i.succ.castSucc (fun x y => x * y)
        (Fin.cons (α := fun _ => G) g t) 0 = g
    have hlt : ((0 : Fin (n + 1)) : ℕ) < (i.succ.castSucc : Fin (n + 2)).val := by
      simp only [Fin.val_zero, Fin.val_castSucc, Fin.val_succ]
      omega
    rw [Fin.contractNth_apply_of_lt _ _ _ _ hlt]
    rfl
  · change Fin.contractNth i.succ.castSucc (fun x y => x * y)
        (Fin.cons (α := fun _ => G) g t) k.succ =
      Fin.contractNth i.castSucc (fun x y => x * y) t k
    by_cases h₁ : k.val < i.val <;> by_cases h₂ : k.val = i.val
    · exact absurd h₂ (ne_of_lt h₁)
    · have hL : k.succ.val < i.succ.castSucc.val := by
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      rw [Fin.contractNth_apply_of_lt _ _ _ _ hL,
        Fin.contractNth_apply_of_lt _ _ _ _ h₁]
      rfl
    · have hL : k.succ.val = i.succ.castSucc.val := by
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      rw [Fin.contractNth_apply_of_eq _ _ _ _ hL,
        Fin.contractNth_apply_of_eq _ _ _ _ h₂]
      rfl
    · have hL : i.succ.castSucc.val < k.succ.val := by
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      have hR : i.castSucc.val < k.val := by
        simp only [Fin.val_castSucc]
        omega
      rw [Fin.contractNth_apply_of_gt _ _ _ _ hL,
        Fin.contractNth_apply_of_gt _ _ _ _ hR]
      rfl

private theorem topMonadPowTupleHomeomorph_muAtPos_snd :
    ∀ (n : ℕ) (X : TopCat.{u}) (j : Fin n)
      (x : ((monadPow (tensorMonad (GTop G)) (n + 1)).obj X : Type _)),
      (topMonadPowTupleHomeomorph (G := G) X n
        ((tensorMonad (GTop G)).muAtPos n j X x)).2 =
      (topMonadPowTupleHomeomorph (G := G) X (n + 1) x).2 := by
  intro n
  induction n with
  | zero =>
      intro X j
      exact Fin.elim0 j
  | succ n ih =>
      intro X j x
      match j with
      | ⟨0, h₀⟩ =>
        have hM : (tensorMonad (GTop G)).muAtPos (n + 1) ⟨0, h₀⟩ X x =
            ((monadPow (tensorMonad (GTop G)) n).map
              ((tensorMonad (GTop G)).μ.app X) x) := rfl
        rw [hM, topMonadPowTupleHomeomorph_succ_apply,
          topMonadPowTupleHomeomorph_succ_apply,
          topMonadPowTupleHomeomorph_map]
        rfl
      | ⟨jv + 1, hj⟩ =>
        have hEq := muAtPos_succ_eq (T := tensorMonad (GTop G)) (n := n)
          (k := (⟨jv, by omega⟩ : Fin n)) (X := X)
        have hM : (tensorMonad (GTop G)).muAtPos (n + 1) ⟨jv + 1, hj⟩ X x =
            (tensorMonad (GTop G)).muAtPos n (⟨jv, by omega⟩ : Fin n)
              ((tensorMonad (GTop G)).obj X) x := by
          rw [hEq]
        rw [hM, topMonadPowTupleHomeomorph_succ_apply,
          topMonadPowTupleHomeomorph_succ_apply]
        exact congrArg (fun p => p.2)
          (ih _ (⟨jv, by omega⟩ : Fin n) x)

private theorem topMonadPowTupleHomeomorph_muAtPos_fst :
    ∀ (n : ℕ) (X : TopCat.{u}) (j : Fin n)
      (x : ((monadPow (tensorMonad (GTop G)) (n + 1)).obj X : Type _)),
      (topMonadPowTupleHomeomorph (G := G) X n
        ((tensorMonad (GTop G)).muAtPos n j X x)).1 =
      topTupleContract G
        ⟨n - 1 - j.val, by have := j.isLt; omega⟩
        (topMonadPowTupleHomeomorph (G := G) X (n + 1) x).1 := by
  intro n
  induction n with
  | zero =>
      intro X j
      exact Fin.elim0 j
  | succ n ih =>
      intro X j x
      match j with
      | ⟨0, h₀⟩ =>
        have hM : (tensorMonad (GTop G)).muAtPos (n + 1) ⟨0, h₀⟩ X x =
            ((monadPow (tensorMonad (GTop G)) n).map
              ((tensorMonad (GTop G)).μ.app X) x) := rfl
        have hm :
            (⟨n + 1 - 1 - (⟨0, h₀⟩ : Fin (n + 1)).val, by omega⟩ :
              Fin (n + 1)) = Fin.last n := by
          apply Fin.ext
          rfl
        let q : (Fin n → G) × (G × G × X) :=
          topMonadPowTupleHomeomorph (G := G)
            ((tensorMonad (GTop G)).obj ((tensorMonad (GTop G)).obj X)) n x
        have hMap : topMonadPowTupleHomeomorph (G := G)
              ((tensorMonad (GTop G)).obj X) n
              (((monadPow (tensorMonad (GTop G)) n).map
                ((tensorMonad (GTop G)).μ.app X)) x) =
            (q.1, (q.2.1 * q.2.2.1, q.2.2.2)) := by
          have h := topMonadPowTupleHomeomorph_map (G := G)
            ((tensorMonad (GTop G)).μ.app X) n x
          change _ = (q.1, ((tensorMonad (GTop G)).μ.app X) q.2) at h
          rw [topTensorMonad_mu_apply] at h
          exact h
        have hInner : topMonadPowTupleHomeomorph (G := G)
              ((tensorMonad (GTop G)).obj X) (n + 1) x =
            (Fin.snoc q.1 q.2.1, q.2.2) := by
          exact topMonadPowTupleHomeomorph_succ_apply
            (G := G) ((tensorMonad (GTop G)).obj X) n x
        have hInput : topMonadPowTupleHomeomorph (G := G) X (n + 2) x =
            (Fin.snoc (Fin.snoc q.1 q.2.1) q.2.2.1, q.2.2.2) := by
          have h := topMonadPowTupleHomeomorph_succ_apply (G := G) X (n + 1) x
          rw [hInner] at h
          exact h
        have hOutput : topMonadPowTupleHomeomorph (G := G) X (n + 1)
              (((monadPow (tensorMonad (GTop G)) n).map
                ((tensorMonad (GTop G)).μ.app X)) x) =
            (Fin.snoc q.1 (q.2.1 * q.2.2.1), q.2.2.2) := by
          have h := topMonadPowTupleHomeomorph_succ_apply (G := G) X n
            (((monadPow (tensorMonad (GTop G)) n).map
              ((tensorMonad (GTop G)).μ.app X)) x)
          rw [hMap] at h
          exact h
        rw [hM, hm, hOutput, hInput]
        funext p
        cases p using Fin.lastCases with
        | last =>
          change Fin.snoc (α := fun _ => G) q.1
              (q.2.1 * q.2.2.1) (Fin.last n) =
            Fin.contractNth (Fin.last n).castSucc (fun x y => x * y)
              (Fin.snoc (α := fun _ => G)
                (Fin.snoc (α := fun _ => G) q.1 q.2.1) q.2.2.1) (Fin.last n)
          rw [Fin.snoc_last]
          rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl]
          rw [Fin.snoc_castSucc, Fin.snoc_last]
          have e : (Fin.last n).succ = Fin.last (n + 1) := rfl
          rw [e, Fin.snoc_last]
        | cast p =>
          change Fin.snoc (α := fun _ => G) q.1
              (q.2.1 * q.2.2.1) p.castSucc =
            Fin.contractNth (Fin.last n).castSucc (fun x y => x * y)
              (Fin.snoc (α := fun _ => G)
                (Fin.snoc (α := fun _ => G) q.1 q.2.1) q.2.2.1) p.castSucc
          have hbelow : (Fin.castSucc p).val < (Fin.last n).val := by
            simp only [Fin.val_castSucc, Fin.val_last]
            exact p.isLt
          rw [Fin.snoc_castSucc]
          rw [Fin.contractNth_apply_of_lt _ _ _ _ hbelow,
            Fin.snoc_castSucc, Fin.snoc_castSucc]
      | ⟨jv + 1, hj⟩ =>
        have hEq := muAtPos_succ_eq (T := tensorMonad (GTop G)) (n := n)
          (k := (⟨jv, by omega⟩ : Fin n)) (X := X)
        have hM : (tensorMonad (GTop G)).muAtPos (n + 1) ⟨jv + 1, hj⟩ X x =
            (tensorMonad (GTop G)).muAtPos n (⟨jv, by omega⟩ : Fin n)
              ((tensorMonad (GTop G)).obj X) x := by
          rw [hEq]
        have hm :
            (⟨n + 1 - 1 - (⟨jv + 1, hj⟩ : Fin (n + 1)).val, by omega⟩ :
              Fin (n + 1)) =
            (⟨n - 1 - jv, by omega⟩ : Fin n).castSucc := by
          apply Fin.ext
          change n + 1 - 1 - (jv + 1) = n - 1 - jv
          omega
        rw [hM, hm, topMonadPowTupleHomeomorph_succ_apply,
          topMonadPowTupleHomeomorph_succ_apply, topTupleContract_snoc,
          Fin.snoc_inj]
        refine ⟨?_, ?_⟩
        · exact ih _ (⟨jv, by omega⟩ : Fin n) x
        · exact congrArg (fun p => p.1)
            (topMonadPowTupleHomeomorph_muAtPos_snd G n _
              (⟨jv, by omega⟩ : Fin n) x)

/-- `muAtPos` contracts the corresponding adjacent entries of the head-first tuple. -/
theorem topMonadPowTupleHomeomorph_muAtPos (n : ℕ) (X : TopCat.{u})
    (j : Fin n)
    (x : ((monadPow (tensorMonad (GTop G)) (n + 1)).obj X : Type _)) :
    topMonadPowTupleHomeomorph (G := G) X n
        ((tensorMonad (GTop G)).muAtPos n j X x) =
      (topTupleContract G ⟨n - 1 - j.val, by have := j.isLt; omega⟩
          (topMonadPowTupleHomeomorph (G := G) X (n + 1) x).1,
        (topMonadPowTupleHomeomorph (G := G) X (n + 1) x).2) := by
  apply Prod.ext
  · exact topMonadPowTupleHomeomorph_muAtPos_fst G n X j x
  · exact topMonadPowTupleHomeomorph_muAtPos_snd G n X j x

/-- `barMuAtPos` contracts entries at its public head-first index. -/
theorem topMonadPowTupleHomeomorph_barMuAtPos (n : ℕ) (X : TopCat.{u})
    (j : Fin n)
    (x : ((monadPow (tensorMonad (GTop G)) (n + 1)).obj X : Type _)) :
    topMonadPowTupleHomeomorph (G := G) X n
        (barMuAtPos (tensorMonad (GTop G)) n j X x) =
      (topTupleContract G j
          (topMonadPowTupleHomeomorph (G := G) X (n + 1) x).1,
        (topMonadPowTupleHomeomorph (G := G) X (n + 1) x).2) := by
  rw [barMuAtPos_rev]
  have h := topMonadPowTupleHomeomorph_muAtPos G n X j.rev x
  have hj : (⟨n - 1 - j.rev.val, by have := j.rev.isLt; omega⟩ : Fin n) = j := by
    apply Fin.ext
    simp only [Fin.val_rev]
    have := j.isLt
    omega
  rw [hj] at h
  exact h

omit [TopologicalSpace G] [ContinuousMul G] in
/-- Inserting below the final coordinate commutes with tuple snoc. -/
theorem topTupleInsert_snoc (n : ℕ) (t : Fin n → G) (g : G)
    (i : Fin (n + 1)) :
    topTupleInsert G i.castSucc (Fin.snoc t g) =
      Fin.snoc (topTupleInsert G i t) g := by
  have hBelow : ∀ {k : ℕ} (v : Fin k → G) (m : Fin (k + 1))
      (j : Fin (k + 1)) (h : j.val < m.val),
      topTupleInsert G m v j = v ⟨j.val, by have := m.isLt; omega⟩ := by
    intro k v m j h
    have hjlast : j ≠ Fin.last k := by
      intro hj
      have hv := congrArg Fin.val hj
      have := m.isLt
      rw [Fin.val_last] at hv
      omega
    unfold topTupleInsert
    rw [Fin.insertNth_apply_below (Fin.lt_def.mpr h)]
    simp only [eq_rec_constant]
    change v (j.castPred hjlast) = v ⟨j.val, by omega⟩
    apply congrArg v
    apply Fin.ext
    exact Fin.coe_castPred j hjlast
  have hAt : ∀ {k : ℕ} (v : Fin k → G) (m : Fin (k + 1)),
      topTupleInsert G m v m = 1 := by
    intro k v m
    unfold topTupleInsert
    rw [Fin.insertNth_apply_same]
  have hAbove : ∀ {k : ℕ} (v : Fin k → G) (m : Fin (k + 1))
      (j : Fin (k + 1)) (h₁ : ¬ j.val < m.val) (h₂ : j.val ≠ m.val),
      topTupleInsert G m v j = v ⟨j.val - 1, by have := j.isLt; omega⟩ := by
    intro k v m j h₁ h₂
    have hlt : m < j := Fin.lt_def.mpr (by omega)
    have hjzero : j ≠ 0 := by
      intro hj
      subst j
      have h := hlt
      change m.val < 0 at h
      exact Nat.not_lt_zero _ h
    unfold topTupleInsert
    rw [Fin.insertNth_apply_above hlt]
    simp only [eq_rec_constant]
    change v (j.pred hjzero) = v ⟨j.val - 1, by omega⟩
    apply congrArg v
    apply Fin.ext
    exact Fin.val_pred j hjzero
  funext j
  cases j using Fin.lastCases with
  | last =>
      have h₁ : ¬ (Fin.last (n + 1)).val < i.castSucc.val := by
        rw [Fin.val_last, Fin.val_castSucc]
        have := i.isLt
        omega
      have h₂ : (Fin.last (n + 1)).val ≠ i.castSucc.val := by
        rw [Fin.val_last, Fin.val_castSucc]
        have := i.isLt
        omega
      rw [hAbove _ _ _ h₁ h₂, Fin.snoc_last]
      have e : (⟨(Fin.last (n + 1)).val - 1, by omega⟩ : Fin (n + 1)) =
          Fin.last n := by
        apply Fin.ext
        change n + 1 - 1 = n
        omega
      rw [e, Fin.snoc_last]
  | cast j =>
      by_cases h₁ : j.val < i.val <;> by_cases h₂ : j.val = i.val
      · exact absurd h₂ (ne_of_lt h₁)
      · have h₁' : (Fin.castSucc j).val < i.castSucc.val := by
          change j.val < i.val
          exact h₁
        rw [hBelow _ _ _ h₁', Fin.snoc_castSucc,
          hBelow _ _ _ h₁]
        have hlt : j.val < n := by have := i.isLt; omega
        simp only [Fin.snoc, Fin.val_castSucc, hlt, dite_true, Fin.castLT]
        rfl
      · have hj : j = i := Fin.ext h₂
        subst hj
        rw [hAt, Fin.snoc_castSucc, hAt]
      · have h₁' : ¬ (Fin.castSucc j).val < i.castSucc.val := by
          change ¬ j.val < i.val
          exact h₁
        have h₂' : (Fin.castSucc j).val ≠ i.castSucc.val := by
          change j.val ≠ i.val
          exact h₂
        rw [hAbove _ _ _ h₁' h₂', Fin.snoc_castSucc,
          hAbove _ _ _ h₁ h₂]
        have hlt : j.val - 1 < n := by
          have := j.isLt
          have := i.isLt
          omega
        simp only [Fin.snoc, Fin.val_castSucc, hlt, dite_true, Fin.castLT]
        rfl

private theorem topMonadPowTupleHomeomorph_etaAtPos_snd :
    ∀ (n : ℕ) (X : TopCat.{u}) (j : Fin (n + 1))
      (x : ((monadPow (tensorMonad (GTop G)) n).obj X : Type _)),
      (topMonadPowTupleHomeomorph (G := G) X (n + 1)
        ((tensorMonad (GTop G)).etaAtPos n j X x)).2 =
      (topMonadPowTupleHomeomorph (G := G) X n x).2 := by
  intro n
  induction n with
  | zero =>
      intro X j x
      have hj : j = (0 : Fin 1) := by
        apply Fin.ext
        have := j.isLt
        omega
      subst hj
      rfl
  | succ n ih =>
      intro X j x
      match j with
      | ⟨0, h₀⟩ =>
        have hM : (tensorMonad (GTop G)).etaAtPos (n + 1) ⟨0, h₀⟩ X x =
            ((monadPow (tensorMonad (GTop G)) (n + 1)).map
              ((tensorMonad (GTop G)).η.app X) x) := rfl
        let q : (Fin (n + 1) → G) × X :=
          topMonadPowTupleHomeomorph (G := G) X (n + 1) x
        have hMap : topMonadPowTupleHomeomorph (G := G)
              ((tensorMonad (GTop G)).obj X) (n + 1)
              (((monadPow (tensorMonad (GTop G)) (n + 1)).map
                ((tensorMonad (GTop G)).η.app X)) x) =
            (q.1, (1, q.2)) := by
          have h := topMonadPowTupleHomeomorph_map (G := G)
            ((tensorMonad (GTop G)).η.app X) (n + 1) x
          change _ = (q.1, ((tensorMonad (GTop G)).η.app X) q.2) at h
          rw [topTensorMonad_eta_apply] at h
          exact h
        have hOutput : topMonadPowTupleHomeomorph (G := G) X (n + 2)
              (((monadPow (tensorMonad (GTop G)) (n + 1)).map
                ((tensorMonad (GTop G)).η.app X)) x) =
            (Fin.snoc q.1 1, q.2) := by
          have h := topMonadPowTupleHomeomorph_succ_apply (G := G) X (n + 1)
            (((monadPow (tensorMonad (GTop G)) (n + 1)).map
              ((tensorMonad (GTop G)).η.app X)) x)
          rw [hMap] at h
          exact h
        rw [hM, hOutput]
      | ⟨jv + 1, hj⟩ =>
        have hEq := etaAtPos_succ_eq (T := tensorMonad (GTop G)) (n := n)
          (k := (⟨jv, by omega⟩ : Fin (n + 1))) (X := X)
        have hM : (tensorMonad (GTop G)).etaAtPos (n + 1) ⟨jv + 1, hj⟩ X x =
            (tensorMonad (GTop G)).etaAtPos n (⟨jv, by omega⟩ : Fin (n + 1))
              ((tensorMonad (GTop G)).obj X) x := by
          rw [hEq]
        rw [hM, topMonadPowTupleHomeomorph_succ_apply,
          topMonadPowTupleHomeomorph_succ_apply]
        exact congrArg (fun p => p.2)
          (ih _ (⟨jv, by omega⟩ : Fin (n + 1)) x)

private theorem topMonadPowTupleHomeomorph_etaAtPos_fst :
    ∀ (n : ℕ) (X : TopCat.{u}) (j : Fin (n + 1))
      (x : ((monadPow (tensorMonad (GTop G)) n).obj X : Type _)),
      (topMonadPowTupleHomeomorph (G := G) X (n + 1)
        ((tensorMonad (GTop G)).etaAtPos n j X x)).1 =
      topTupleInsert G ⟨n - j.val, by have := j.isLt; omega⟩
        (topMonadPowTupleHomeomorph (G := G) X n x).1 := by
  intro n
  induction n with
  | zero =>
      intro X j x
      have hj : j = (0 : Fin 1) := by
        apply Fin.ext
        have := j.isLt
        omega
      subst hj
      funext p
      have hp : p = (0 : Fin 1) := by
        apply Fin.ext
        have := p.isLt
        omega
      subst hp
      rfl
  | succ n ih =>
      intro X j x
      match j with
      | ⟨0, h₀⟩ =>
        have hM : (tensorMonad (GTop G)).etaAtPos (n + 1) ⟨0, h₀⟩ X x =
            ((monadPow (tensorMonad (GTop G)) (n + 1)).map
              ((tensorMonad (GTop G)).η.app X) x) := rfl
        have hm : (⟨n + 1 - (⟨0, h₀⟩ : Fin (n + 2)).val, by omega⟩ :
            Fin (n + 2)) = Fin.last (n + 1) := by
          apply Fin.ext
          rfl
        let q : (Fin (n + 1) → G) × X :=
          topMonadPowTupleHomeomorph (G := G) X (n + 1) x
        have hMap : topMonadPowTupleHomeomorph (G := G)
              ((tensorMonad (GTop G)).obj X) (n + 1)
              (((monadPow (tensorMonad (GTop G)) (n + 1)).map
                ((tensorMonad (GTop G)).η.app X)) x) =
            (q.1, (1, q.2)) := by
          have h := topMonadPowTupleHomeomorph_map (G := G)
            ((tensorMonad (GTop G)).η.app X) (n + 1) x
          change _ = (q.1, ((tensorMonad (GTop G)).η.app X) q.2) at h
          rw [topTensorMonad_eta_apply] at h
          exact h
        have hOutput : topMonadPowTupleHomeomorph (G := G) X (n + 2)
              (((monadPow (tensorMonad (GTop G)) (n + 1)).map
                ((tensorMonad (GTop G)).η.app X)) x) =
            (Fin.snoc q.1 1, q.2) := by
          have h := topMonadPowTupleHomeomorph_succ_apply (G := G) X (n + 1)
            (((monadPow (tensorMonad (GTop G)) (n + 1)).map
              ((tensorMonad (GTop G)).η.app X)) x)
          rw [hMap] at h
          exact h
        rw [hM, hm, hOutput]
        change Fin.snoc (α := fun _ => G) q.1 1 =
          topTupleInsert G (Fin.last (n + 1)) q.1
        funext p
        cases p using Fin.lastCases with
        | last =>
          rw [Fin.snoc_last]
          unfold topTupleInsert
          rw [Fin.insertNth_apply_same]
        | cast p =>
          have hpLast : p.castSucc ≠ Fin.last (n + 1) := by
            apply Fin.ne_of_lt
            change p.val < n + 1
            exact p.isLt
          rw [Fin.snoc_castSucc]
          unfold topTupleInsert
          rw [Fin.insertNth_apply_below]
          · simp only [eq_rec_constant]
            change q.1 ((p.castSucc).castPred hpLast) = q.1 p
            apply congrArg q.1
            apply Fin.ext
            exact Fin.coe_castPred p.castSucc hpLast
          · simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_last]
            exact p.isLt
      | ⟨jv + 1, hj⟩ =>
        let j₀ : Fin (n + 1) := ⟨jv, by omega⟩
        let i₀ : Fin (n + 1) := ⟨n - jv, by omega⟩
        let q : (Fin n → G) × (G × X) :=
          topMonadPowTupleHomeomorph (G := G)
            ((tensorMonad (GTop G)).obj X) n x
        have hEq := etaAtPos_succ_eq (T := tensorMonad (GTop G)) (n := n)
          (k := j₀) (X := X)
        have hM : (tensorMonad (GTop G)).etaAtPos (n + 1) ⟨jv + 1, hj⟩ X x =
            (tensorMonad (GTop G)).etaAtPos n j₀
              ((tensorMonad (GTop G)).obj X) x := by
          rw [hEq]
        have hm : (⟨n + 1 - (⟨jv + 1, hj⟩ : Fin (n + 2)).val, by omega⟩ :
            Fin (n + 2)) = i₀.castSucc := by
          apply Fin.ext
          change n + 1 - (jv + 1) = n - jv
          omega
        have hIH : topMonadPowTupleHomeomorph (G := G)
              ((tensorMonad (GTop G)).obj X) (n + 1)
              ((tensorMonad (GTop G)).etaAtPos n j₀
                ((tensorMonad (GTop G)).obj X) x) =
            (topTupleInsert G i₀ q.1, q.2) := by
          apply Prod.ext
          · exact ih ((tensorMonad (GTop G)).obj X) j₀ x
          · exact topMonadPowTupleHomeomorph_etaAtPos_snd G n
              ((tensorMonad (GTop G)).obj X) j₀ x
        have hInput : topMonadPowTupleHomeomorph (G := G) X (n + 1) x =
            (Fin.snoc q.1 q.2.1, q.2.2) :=
          topMonadPowTupleHomeomorph_succ_apply (G := G) X n x
        have hOutput : topMonadPowTupleHomeomorph (G := G) X (n + 2)
              ((tensorMonad (GTop G)).etaAtPos n j₀
                ((tensorMonad (GTop G)).obj X) x) =
            (Fin.snoc (topTupleInsert G i₀ q.1) q.2.1, q.2.2) := by
          have h := topMonadPowTupleHomeomorph_succ_apply (G := G) X (n + 1)
            ((tensorMonad (GTop G)).etaAtPos n j₀
              ((tensorMonad (GTop G)).obj X) x)
          rw [hIH] at h
          exact h
        rw [hM, hm, hOutput, hInput]
        exact (topTupleInsert_snoc G n q.1 q.2.1 i₀).symm

/-- `etaAtPos` inserts a unit at the corresponding head-first tuple index. -/
theorem topMonadPowTupleHomeomorph_etaAtPos (n : ℕ) (X : TopCat.{u})
    (j : Fin (n + 1))
    (x : ((monadPow (tensorMonad (GTop G)) n).obj X : Type _)) :
    topMonadPowTupleHomeomorph (G := G) X (n + 1)
        ((tensorMonad (GTop G)).etaAtPos n j X x) =
      (topTupleInsert G ⟨n - j.val, by have := j.isLt; omega⟩
          (topMonadPowTupleHomeomorph (G := G) X n x).1,
        (topMonadPowTupleHomeomorph (G := G) X n x).2) := by
  apply Prod.ext
  · exact topMonadPowTupleHomeomorph_etaAtPos_fst G n X j x
  · exact topMonadPowTupleHomeomorph_etaAtPos_snd G n X j x

/-- `barEtaAtPos` inserts the unit at its public head-first index. -/
theorem topMonadPowTupleHomeomorph_barEtaAtPos (n : ℕ) (X : TopCat.{u})
    (j : Fin (n + 1))
    (x : ((monadPow (tensorMonad (GTop G)) n).obj X : Type _)) :
    topMonadPowTupleHomeomorph (G := G) X (n + 1)
        (barEtaAtPos (tensorMonad (GTop G)) n j X x) =
      (topTupleInsert G j
          (topMonadPowTupleHomeomorph (G := G) X n x).1,
        (topMonadPowTupleHomeomorph (G := G) X n x).2) := by
  rw [barEtaAtPos_rev]
  have h := topMonadPowTupleHomeomorph_etaAtPos G n X j.rev x
  have hj : (⟨n - j.rev.val, by have := j.rev.isLt; omega⟩ : Fin (n + 1)) = j := by
    apply Fin.ext
    simp only [Fin.val_rev]
    have := j.isLt
    omega
  rw [hj] at h
  exact h

omit [TopologicalSpace G] [ContinuousMul G] in
/-- Inserting after a fixed head coordinate commutes with tuple cons. -/
theorem topTupleInsert_cons {n : ℕ} (i : Fin (n + 1)) (g : G)
    (t : Fin n → G) :
    topTupleInsert G i.succ (Fin.cons (α := fun _ => G) g t) =
      Fin.cons (α := fun _ => G) g (topTupleInsert G i t) := by
  unfold topTupleInsert
  exact Fin.insertNth_succ_cons i 1 g t

omit [TopologicalSpace G] [Monoid G] [ContinuousMul G] in
private theorem topFinInit_cons {n : ℕ} (g : G) (t : Fin (n + 1) → G) :
    Fin.init (Fin.cons (α := fun _ => G) g t) =
      Fin.cons (α := fun _ => G) g (Fin.init t) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Mapping a final tensor-monad action preserves the tuple and removes its
last coordinate from the successor reader. -/
theorem topMonadPowTupleHomeomorph_map_last_fst
    (n : ℕ) {X Y : TopCat.{u}} (f : (tensorMonad (GTop G)).obj X ⟶ Y)
    (x : ((monadPow (tensorMonad (GTop G)) (n + 1)).obj X : Type _)) :
    (topMonadPowTupleHomeomorph (G := G) Y n
      (((monadPow (tensorMonad (GTop G)) n).map f) x)).1 =
      Fin.init (topMonadPowTupleHomeomorph (G := G) X (n + 1) x).1 := by
  let q : (Fin n → G) × (G × X) :=
    topMonadPowTupleHomeomorph (G := G) ((tensorMonad (GTop G)).obj X) n x
  have hMap : topMonadPowTupleHomeomorph (G := G) Y n
        (((monadPow (tensorMonad (GTop G)) n).map f) x) =
      (q.1, f q.2) :=
    topMonadPowTupleHomeomorph_map (G := G) f n x
  have hInput : topMonadPowTupleHomeomorph (G := G) X (n + 1) x =
      (Fin.snoc q.1 q.2.1, q.2.2) :=
    topMonadPowTupleHomeomorph_succ_apply (G := G) X n x
  rw [hMap, hInput, Fin.init_snoc]

omit [TopologicalSpace G] [Monoid G] [ContinuousMul G] in
private theorem topFinTail_snoc {n : ℕ} (t : Fin (n + 1) → G) (g : G) :
    Fin.tail (Fin.snoc (α := fun _ => G) t g) =
      Fin.snoc (α := fun _ => G) (Fin.tail t) g := by
  funext j
  cases j using Fin.lastCases with
  | last =>
      have h : (Fin.last n).succ = Fin.last (n + 1) := rfl
      simp only [Fin.tail]
      rw [h, Fin.snoc_last, Fin.snoc_last]
  | cast j =>
      simp only [Fin.tail]
      have h : (Fin.castSucc j).succ = Fin.castSucc j.succ :=
        (Fin.castSucc_succ j).symm
      rw [h, Fin.snoc_castSucc, Fin.snoc_castSucc]
      rfl

private theorem BBarRightActionPow_snd :
    ∀ (n : ℕ) (X : TopCat.{u})
      (x : ((tensorLeft topPoint.{u}).obj
        ((monadPow (tensorMonad (GTop G)) (n + 1)).obj X) : Type _)),
      (topMonadPowTupleHomeomorph (G := G) X n
        ((rightActionPow (tensorMonad (GTop G))
          (rightModuleOfRightAction topPoint.{u} (GTop G)
            (topPointRightAction G) (topPointRightAction_one G)
            (topPointRightAction_assoc G)) n X) x).2).2 =
      (topMonadPowTupleHomeomorph (G := G) X (n + 1) x.2).2 := by
  intro n
  induction n with
  | zero =>
      intro X x
      rfl
  | succ n ih =>
      intro X x
      rw [rightActionPow_succ, topMonadPowTupleHomeomorph_succ_apply,
        topMonadPowTupleHomeomorph_succ_apply]
      exact congrArg (fun p => p.2) (ih ((tensorMonad (GTop G)).obj X) x)

private theorem BBarRightActionPow_fst :
    ∀ (n : ℕ) (X : TopCat.{u})
      (x : ((tensorLeft topPoint.{u}).obj
        ((monadPow (tensorMonad (GTop G)) (n + 1)).obj X) : Type _)),
      (topMonadPowTupleHomeomorph (G := G) X n
        ((rightActionPow (tensorMonad (GTop G))
          (rightModuleOfRightAction topPoint.{u} (GTop G)
            (topPointRightAction G) (topPointRightAction_one G)
            (topPointRightAction_assoc G)) n X) x).2).1 =
      Fin.tail (topMonadPowTupleHomeomorph (G := G) X (n + 1) x.2).1 := by
  intro n
  induction n with
  | zero =>
      intro X x
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      intro X x
      rw [rightActionPow_succ, topMonadPowTupleHomeomorph_succ_apply,
        topMonadPowTupleHomeomorph_succ_apply, topFinTail_snoc,
        Fin.snoc_inj]
      refine ⟨?_, ?_⟩
      · exact ih ((tensorMonad (GTop G)).obj X) x
      · exact congrArg (fun p => p.1)
          (BBarRightActionPow_snd G n ((tensorMonad (GTop G)).obj X) x)

private theorem EBarRegularRightActionPow_snd :
    ∀ (n : ℕ) (X : TopCat.{u})
      (x : ((tensorMonad (GTop G)).obj
        ((monadPow (tensorMonad (GTop G)) (n + 1)).obj X) : Type _)),
      (topMonadPowTupleHomeomorph (G := G) X n
        ((rightActionPow (tensorMonad (GTop G))
          (RightModule.regular (tensorMonad (GTop G))) n X) x).2).2 =
      (topMonadPowTupleHomeomorph (G := G) X (n + 1) x.2).2 := by
  intro n
  induction n with
  | zero =>
      intro X x
      rfl
  | succ n ih =>
      intro X x
      rw [rightActionPow_succ, topMonadPowTupleHomeomorph_succ_apply,
        topMonadPowTupleHomeomorph_succ_apply]
      exact congrArg (fun p => p.2) (ih ((tensorMonad (GTop G)).obj X) x)

private theorem EBarRegularRightActionPow_fst :
    ∀ (n : ℕ) (X : TopCat.{u})
      (x : ((tensorMonad (GTop G)).obj
        ((monadPow (tensorMonad (GTop G)) (n + 1)).obj X) : Type _)),
      Fin.cons (α := fun _ => G)
          ((rightActionPow (tensorMonad (GTop G))
            (RightModule.regular (tensorMonad (GTop G))) n X) x).1
          (topMonadPowTupleHomeomorph (G := G) X n
            ((rightActionPow (tensorMonad (GTop G))
              (RightModule.regular (tensorMonad (GTop G))) n X) x).2).1 =
        topTupleContract G 0
          (Fin.cons (α := fun _ => G) x.1
            (topMonadPowTupleHomeomorph (G := G) X (n + 1) x.2).1) := by
  intro n
  induction n with
  | zero =>
      intro X x
      funext j
      have hj : j = (0 : Fin 1) := by
        apply Fin.ext
        have := j.isLt
        omega
      subst hj
      change x.1 * x.2.1 =
        Fin.contractNth (0 : Fin 1).castSucc (fun a b => a * b)
          (Fin.cons (α := fun _ => G) x.1
            (Fin.snoc (α := fun _ => G) (fun i => Fin.elim0 i) x.2.1)) 0
      rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl]
      rfl
  | succ n ih =>
      intro X x
      rw [rightActionPow_succ, topMonadPowTupleHomeomorph_succ_apply,
        topMonadPowTupleHomeomorph_succ_apply]
      rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_snoc_eq_snoc_cons]
      change Fin.snoc (α := fun _ => G)
          (Fin.cons (α := fun _ => G)
            ((rightActionPow (tensorMonad (GTop G))
              (RightModule.regular (tensorMonad (GTop G))) n
              ((tensorMonad (GTop G)).obj X)) x).1
            (topMonadPowTupleHomeomorph (G := G)
              ((tensorMonad (GTop G)).obj X) n
              ((rightActionPow (tensorMonad (GTop G))
                (RightModule.regular (tensorMonad (GTop G))) n
                ((tensorMonad (GTop G)).obj X)) x).2).1)
          (topMonadPowTupleHomeomorph (G := G)
            ((tensorMonad (GTop G)).obj X) n
            ((rightActionPow (tensorMonad (GTop G))
              (RightModule.regular (tensorMonad (GTop G))) n
              ((tensorMonad (GTop G)).obj X)) x).2).2.1 =
        topTupleContract G (0 : Fin (n + 2))
          (Fin.snoc (α := fun _ => G)
            (Fin.cons (α := fun _ => G) x.1
              (topMonadPowTupleHomeomorph (G := G)
                ((tensorMonad (GTop G)).obj X) (n + 1) x.2).1)
            (topMonadPowTupleHomeomorph (G := G)
              ((tensorMonad (GTop G)).obj X) (n + 1) x.2).2.1)
      have hzero : (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc := rfl
      rw [hzero, topTupleContract_snoc, ih]
      rw [Fin.snoc_inj]
      refine ⟨rfl, ?_⟩
      exact congrArg (fun p => p.1)
          (EBarRegularRightActionPow_snd G n
            ((tensorMonad (GTop G)).obj X) x)

/-- Stable `TopCat` degree isomorphism for the topological classifying bar. -/
noncomputable def BBarDegreeIso (n : ℕ) :
    (BBar G).obj (Opposite.op (SimplexCategory.mk n)) ≅
      TopCat.of (Fin n → G) :=
  TopCat.isoOfHomeo (BBarDegreeHomeomorph G n)

/-- Stable `TopCat` degree isomorphism for the topological universal bar. -/
noncomputable def EBarDegreeIso (n : ℕ) :
    (EBar G).obj (Opposite.op (SimplexCategory.mk n)) ≅
      TopCat.of (Fin (n + 1) → G) :=
  TopCat.isoOfHomeo (EBarDegreeHomeomorph G n)

/-- Zeroth face of the topological classifying bar. -/
theorem BBar_d0 (n : ℕ) :
    (BBar G).map (SimplexCategory.δ (0 : Fin (n + 2))).op =
      barFaceApp
        (R := rightModuleOfRightAction topPoint.{u} (GTop G)
          (topPointRightAction G) (topPointRightAction_one G)
          (topPointRightAction_assoc G))
        (L := leftPointModule (GTop G) topPoint.{u}) n 0 topBarIndex := by
  exact classifyingBar_d0 (GTop G) topPoint.{u} (topPointRightAction G)
    (topPointRightAction_one G) (topPointRightAction_assoc G) n topBarIndex

/-- Last face of the topological classifying bar. -/
theorem BBar_dLast (n : ℕ) :
    (BBar G).map (SimplexCategory.δ (Fin.last (n + 1))).op =
      barFaceApp
        (R := rightModuleOfRightAction topPoint.{u} (GTop G)
          (topPointRightAction G) (topPointRightAction_one G)
          (topPointRightAction_assoc G))
        (L := leftPointModule (GTop G) topPoint.{u}) n (Fin.last (n + 1))
          topBarIndex := by
  exact classifyingBar_dLast (GTop G) topPoint.{u} (topPointRightAction G)
    (topPointRightAction_one G) (topPointRightAction_assoc G) n topBarIndex

/-- Interior face of the topological classifying bar. -/
theorem BBar_dInterior (n : ℕ) (k : Fin n) :
    (BBar G).map (SimplexCategory.δ (k.succ.castSucc : Fin (n + 2))).op =
      (tensorLeft topPoint.{u}).map
        (barMuAtPos (tensorMonad (GTop G)) n k
          ((leftPointModule (GTop G) topPoint.{u}).functor.obj topBarIndex)) := by
  exact classifyingBar_dInterior (GTop G) topPoint.{u} (topPointRightAction G)
    (topPointRightAction_one G) (topPointRightAction_assoc G) n k topBarIndex

/-- Degeneracy of the topological classifying bar. -/
theorem BBar_s (n : ℕ) (i : Fin (n + 1)) :
    (BBar G).map (SimplexCategory.σ i).op =
      (tensorLeft topPoint.{u}).map
        (barEtaAtPos (tensorMonad (GTop G)) n i topPoint.{u}) := by
  exact classifyingBar_s (GTop G) topPoint.{u} (topPointRightAction G)
    (topPointRightAction_one G) (topPointRightAction_assoc G) n i topBarIndex

/-- Zeroth face of the topological universal bar. -/
theorem EBar_d0 (n : ℕ) :
    (EBar G).map (SimplexCategory.δ (0 : Fin (n + 2))).op =
      barFaceApp
        (R := rightModuleOfRightAction (GTop G) (GTop G) MonObj.mul
          (MonObj.mul_one (GTop G)) ((MonObj.mul_assoc (GTop G)).symm))
        (L := leftPointModule (GTop G) topPoint.{u}) n 0 topBarIndex := by
  exact universalBar_d0 (GTop G) topPoint.{u} n topBarIndex

/-- Last face of the topological universal bar. -/
theorem EBar_dLast (n : ℕ) :
    (EBar G).map (SimplexCategory.δ (Fin.last (n + 1))).op =
      barFaceApp
        (R := rightModuleOfRightAction (GTop G) (GTop G) MonObj.mul
          (MonObj.mul_one (GTop G)) ((MonObj.mul_assoc (GTop G)).symm))
        (L := leftPointModule (GTop G) topPoint.{u}) n (Fin.last (n + 1))
          topBarIndex := by
  exact universalBar_dLast (GTop G) topPoint.{u} n topBarIndex

/-- Interior face of the topological universal bar. -/
theorem EBar_dInterior (n : ℕ) (k : Fin n) :
    (EBar G).map (SimplexCategory.δ (k.succ.castSucc : Fin (n + 2))).op =
      (tensorLeft (GTop G)).map
        (barMuAtPos (tensorMonad (GTop G)) n k
          ((leftPointModule (GTop G) topPoint.{u}).functor.obj topBarIndex)) := by
  exact universalBar_dInterior (GTop G) topPoint.{u} n k topBarIndex

/-- Degeneracy of the topological universal bar. -/
theorem EBar_s (n : ℕ) (i : Fin (n + 1)) :
    (EBar G).map (SimplexCategory.σ i).op =
      (tensorLeft (GTop G)).map
        (barEtaAtPos (tensorMonad (GTop G)) n i topPoint.{u}) := by
  exact universalBar_s (GTop G) topPoint.{u} n i topBarIndex

/-- Components of the topological universal-bundle map are evaluations of the strict map. -/
@[simp]
theorem EBarToBBar_app (Δ : SimplexCategoryᵒᵖ) :
    (EBarToBBar G).app Δ = topBarEvaluation.map
      ((universalBundle (GTop G) topPoint.{u} (topPointRightAction G)
        (topPointRightAction_one G) (topPointRightAction_assoc G)
        (topAugmentation G) (topAugmentation_compat G)).app Δ) :=
  rfl

/-- The zeroth BBar face removes the head coordinate. -/
theorem BBarDegreeHomeomorph_d0 (n : ℕ)
    (x : ((BBar G).obj (Opposite.op (SimplexCategory.mk (n + 1))) : Type _)) :
    BBarDegreeHomeomorph G n
        ((BBar G).map (SimplexCategory.δ (0 : Fin (n + 2))).op x) =
      Fin.tail (BBarDegreeHomeomorph G (n + 1) x) := by
  rw [BBar_d0]
  rw [barFaceApp_of_val_zero (hi := rfl)]
  rw [BBarDegreeHomeomorph_apply, BBarDegreeHomeomorph_apply]
  change (topMonadPowTupleHomeomorph (G := G) topPoint.{u} n
      ((rightActionPow (tensorMonad (GTop G))
        (rightModuleOfRightAction topPoint.{u} (GTop G)
          (topPointRightAction G) (topPointRightAction_one G)
          (topPointRightAction_assoc G)) n topPoint.{u}) x).2).1 = _
  exact BBarRightActionPow_fst G n topPoint.{u} x

/-- Zeroth-face formula expressed with the stable remove-coordinate API. -/
theorem BBarDegreeHomeomorph_d0_remove (n : ℕ)
    (x : ((BBar G).obj (Opposite.op (SimplexCategory.mk (n + 1))) : Type _)) :
    BBarDegreeHomeomorph G n
        ((BBar G).map (SimplexCategory.δ (0 : Fin (n + 2))).op x) =
      topTupleRemove G 0 (BBarDegreeHomeomorph G (n + 1) x) := by
  rw [topTupleRemove, Fin.removeNth_zero]
  exact BBarDegreeHomeomorph_d0 G n x

/-- The last BBar face removes the final head-first tuple coordinate. -/
theorem BBarDegreeHomeomorph_dLast (n : ℕ)
    (x : ((BBar G).obj (Opposite.op (SimplexCategory.mk (n + 1))) : Type _)) :
    BBarDegreeHomeomorph G n
        ((BBar G).map (SimplexCategory.δ (Fin.last (n + 1))).op x) =
      Fin.init (BBarDegreeHomeomorph G (n + 1) x) := by
  rw [BBar_dLast]
  rw [barFaceApp_of_val_last (hi := rfl)]
  rw [BBarDegreeHomeomorph_apply, BBarDegreeHomeomorph_apply]
  change (topMonadPowTupleHomeomorph (G := G) topPoint.{u} n
      (((monadPow (tensorMonad (GTop G)) n).map
        ((leftPointModule (GTop G) topPoint.{u}).action.app topBarIndex)) x.2)).1 = _
  exact topMonadPowTupleHomeomorph_map_last_fst G n
    ((leftPointModule (GTop G) topPoint.{u}).action.app topBarIndex) x.2

/-- Last-face formula expressed with the stable remove-coordinate API. -/
theorem BBarDegreeHomeomorph_dLast_remove (n : ℕ)
    (x : ((BBar G).obj (Opposite.op (SimplexCategory.mk (n + 1))) : Type _)) :
    BBarDegreeHomeomorph G n
        ((BBar G).map (SimplexCategory.δ (Fin.last (n + 1))).op x) =
      topTupleRemove G (Fin.last n) (BBarDegreeHomeomorph G (n + 1) x) := by
  rw [topTupleRemove, Fin.removeNth_last]
  exact BBarDegreeHomeomorph_dLast G n x

/-- Interior BBar faces multiply adjacent entries in head-first order. -/
theorem BBarDegreeHomeomorph_dInterior (n : ℕ) (k : Fin n)
    (x : ((BBar G).obj (Opposite.op (SimplexCategory.mk (n + 1))) : Type _)) :
    BBarDegreeHomeomorph G n
        ((BBar G).map
          (SimplexCategory.δ (k.succ.castSucc : Fin (n + 2))).op x) =
      topTupleContract G k (BBarDegreeHomeomorph G (n + 1) x) := by
  rw [BBar_dInterior]
  rw [BBarDegreeHomeomorph_apply, BBarDegreeHomeomorph_apply]
  change (topMonadPowTupleHomeomorph (G := G) topPoint.{u} n
      (barMuAtPos (tensorMonad (GTop G)) n k topPoint.{u} x.2)).1 = _
  exact congrArg (fun p => p.1)
    (topMonadPowTupleHomeomorph_barMuAtPos G n topPoint.{u} k x.2)

/-- BBar degeneracies insert the monoid unit in head-first order. -/
theorem BBarDegreeHomeomorph_s (n : ℕ) (i : Fin (n + 1))
    (x : ((BBar G).obj (Opposite.op (SimplexCategory.mk n)) : Type _)) :
    BBarDegreeHomeomorph G (n + 1)
        ((BBar G).map (SimplexCategory.σ i).op x) =
      topTupleInsert G i (BBarDegreeHomeomorph G n x) := by
  rw [BBar_s]
  rw [BBarDegreeHomeomorph_apply, BBarDegreeHomeomorph_apply]
  change (topMonadPowTupleHomeomorph (G := G) topPoint.{u} (n + 1)
      (barEtaAtPos (tensorMonad (GTop G)) n i topPoint.{u} x.2)).1 = _
  exact congrArg (fun p => p.1)
    (topMonadPowTupleHomeomorph_barEtaAtPos G n topPoint.{u} i x.2)

/-- The zeroth EBar face multiplies the outer regular coordinate with the head. -/
theorem EBarDegreeHomeomorph_d0 (n : ℕ)
    (x : ((EBar G).obj (Opposite.op (SimplexCategory.mk (n + 1))) : Type _)) :
    EBarDegreeHomeomorph G n
        ((EBar G).map (SimplexCategory.δ (0 : Fin (n + 2))).op x) =
      topTupleContract G 0 (EBarDegreeHomeomorph G (n + 1) x) := by
  change G × ((monadPow (tensorMonad (GTop G)) (n + 1)).obj topPoint.{u} : Type _) at x
  rw [EBar_d0]
  rw [barFaceApp_of_val_zero (hi := rfl)]
  change Fin.cons (α := fun _ => G)
      ((rightActionPow (tensorMonad (GTop G))
        (RightModule.regular (tensorMonad (GTop G))) n topPoint.{u}) x).1
      (topMonadPowTupleHomeomorph (G := G) topPoint.{u} n
        ((rightActionPow (tensorMonad (GTop G))
          (RightModule.regular (tensorMonad (GTop G))) n topPoint.{u}) x).2).1 =
    topTupleContract G 0 (Fin.cons (α := fun _ => G) x.1
      (topMonadPowTupleHomeomorph (G := G) topPoint.{u} (n + 1) x.2).1)
  exact EBarRegularRightActionPow_fst G n topPoint.{u} x

/-- Interior EBar faces multiply adjacent entries after the outer regular coordinate. -/
theorem EBarDegreeHomeomorph_dInterior (n : ℕ) (k : Fin n)
    (x : ((EBar G).obj (Opposite.op (SimplexCategory.mk (n + 1))) : Type _)) :
    EBarDegreeHomeomorph G n
        ((EBar G).map
          (SimplexCategory.δ (k.succ.castSucc : Fin (n + 2))).op x) =
      topTupleContract G k.succ (EBarDegreeHomeomorph G (n + 1) x) := by
  rw [EBar_dInterior]
  rw [EBarDegreeHomeomorph_apply, EBarDegreeHomeomorph_apply]
  change Fin.cons (α := fun _ => G) x.1
      (topMonadPowTupleHomeomorph (G := G) topPoint.{u} n
        (barMuAtPos (tensorMonad (GTop G)) n k topPoint.{u} x.2)).1 =
    topTupleContract G k.succ (Fin.cons (α := fun _ => G) x.1
      (topMonadPowTupleHomeomorph (G := G) topPoint.{u} (n + 1) x.2).1)
  have h := congrArg (fun p => p.1)
    (topMonadPowTupleHomeomorph_barMuAtPos G n topPoint.{u} k x.2)
  rw [h]
  exact (topTupleContract_cons G n
    (topMonadPowTupleHomeomorph (G := G) topPoint.{u} (n + 1) x.2).1 x.1 k).symm

/-- The last EBar face removes the final head-first tuple coordinate. -/
theorem EBarDegreeHomeomorph_dLast (n : ℕ)
    (x : ((EBar G).obj (Opposite.op (SimplexCategory.mk (n + 1))) : Type _)) :
    EBarDegreeHomeomorph G n
        ((EBar G).map (SimplexCategory.δ (Fin.last (n + 1))).op x) =
      Fin.init (EBarDegreeHomeomorph G (n + 1) x) := by
  change G × ((monadPow (tensorMonad (GTop G)) (n + 1)).obj topPoint.{u} : Type _) at x
  let f : (tensorMonad (GTop G)).obj topPoint.{u} ⟶ topPoint.{u} :=
    (leftPointModule (GTop G) topPoint.{u}).action.app topBarIndex
  rw [EBar_dLast]
  rw [barFaceApp_of_val_last (hi := rfl)]
  change Fin.cons (α := fun _ => G) x.1
      (topMonadPowTupleHomeomorph (G := G) topPoint.{u} n
        (((monadPow (tensorMonad (GTop G)) n).map f) x.2)).1 =
    Fin.init (Fin.cons (α := fun _ => G) x.1
      (topMonadPowTupleHomeomorph (G := G) topPoint.{u} (n + 1) x.2).1)
  have h := topMonadPowTupleHomeomorph_map_last_fst G n
    (X := topPoint.{u}) (Y := topPoint.{u}) f x.2
  rw [h, topFinInit_cons]

/-- Last EBar face expressed with the stable remove-coordinate API. -/
theorem EBarDegreeHomeomorph_dLast_remove (n : ℕ)
    (x : ((EBar G).obj (Opposite.op (SimplexCategory.mk (n + 1))) : Type _)) :
    EBarDegreeHomeomorph G n
        ((EBar G).map (SimplexCategory.δ (Fin.last (n + 1))).op x) =
      topTupleRemove G (Fin.last (n + 1))
        (EBarDegreeHomeomorph G (n + 1) x) := by
  rw [topTupleRemove, Fin.removeNth_last]
  exact EBarDegreeHomeomorph_dLast G n x

/-- EBar degeneracies insert the unit after the outer regular coordinate. -/
theorem EBarDegreeHomeomorph_s (n : ℕ) (i : Fin (n + 1))
    (x : ((EBar G).obj (Opposite.op (SimplexCategory.mk n)) : Type _)) :
    EBarDegreeHomeomorph G (n + 1)
        ((EBar G).map (SimplexCategory.σ i).op x) =
      topTupleInsert G i.succ (EBarDegreeHomeomorph G n x) := by
  rw [EBar_s]
  rw [EBarDegreeHomeomorph_apply, EBarDegreeHomeomorph_apply]
  change Fin.cons (α := fun _ => G) x.1
      (topMonadPowTupleHomeomorph (G := G) topPoint.{u} (n + 1)
        (barEtaAtPos (tensorMonad (GTop G)) n i topPoint.{u} x.2)).1 =
    topTupleInsert G i.succ (Fin.cons (α := fun _ => G) x.1
      (topMonadPowTupleHomeomorph (G := G) topPoint.{u} n x.2).1)
  have h := congrArg (fun p => p.1)
    (topMonadPowTupleHomeomorph_barEtaAtPos G n topPoint.{u} i x.2)
  rw [h]
  exact (topTupleInsert_cons G i x.1
    (topMonadPowTupleHomeomorph (G := G) topPoint.{u} n x.2).1).symm

/-- Unified head-first coordinate formula for every EBar face. -/
theorem EBarDegreeHomeomorph_face (n : ℕ) (i : Fin (n + 2))
    (x : ((EBar G).obj (Opposite.op (SimplexCategory.mk (n + 1))) : Type _)) :
    EBarDegreeHomeomorph G n
        ((EBar G).map (SimplexCategory.δ i).op x) =
      Fin.cases
        (topTupleContract G 0 (EBarDegreeHomeomorph G (n + 1) x))
        (fun j => Fin.lastCases
          (topTupleRemove G (Fin.last (n + 1))
            (EBarDegreeHomeomorph G (n + 1) x))
          (fun k => topTupleContract G k.succ
            (EBarDegreeHomeomorph G (n + 1) x)) j) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cases_zero]
    exact EBarDegreeHomeomorph_d0 G n x
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [Fin.cases_succ, Fin.lastCases_last]
      have hLast : (Fin.last n).succ = Fin.last (n + 1) := rfl
      rw [hLast]
      exact EBarDegreeHomeomorph_dLast_remove G n x
    · simp only [Fin.cases_succ, Fin.lastCases_castSucc]
      rw [Fin.succ_castSucc]
      exact EBarDegreeHomeomorph_dInterior G n k x

end Monad
end CategoryTheory

end
