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
# Topological classifying and universal bar constructions

Let G be a monoid with a topology and continuous multiplication. In the cartesian category of
topological spaces, the simplicial bars B(*,G,*) and B(G,G,*) have degree spaces homeomorphic
to Gⁿ and Gⁿ⁺¹, respectively. Continuous monoid homomorphisms induce simplicial maps,
compatible with the universal-to-classifying bar map and augmentation to the point.

In classifying-bar tuple coordinates, the first and last faces delete the first and last
entries, interior faces multiply adjacent entries in order, and degeneracies insert 1. In
universal-bar coordinates, the regular leading factor is retained by the interior faces and
degeneracies: every face except the last multiplies an adjacent pair, the last deletes the
last entry, and the i-th degeneracy inserts 1 at position i+1. The power-coordinate laws
account for the reversal between monad positions and displayed tuple indices.

The augmented universal bar has an extra degeneracy, a section of its augmentation and a
simplicial contraction homotopy from the augmentation-section composite to its identity.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite

namespace CategoryTheory
namespace Monad

universe u

variable (G : Type u) [TopologicalSpace G] [Monoid G] [ContinuousMul G]

/-- The topological space underlying a monoid.

Bundle G with its specified topology as an object of TopCat. -/
@[reducible]
def GTop : TopCat.{u} :=
  TopCat.of G

/-- The unit map of the topological monoid object.

The map from the cartesian tensor unit to G is the constant continuous map with value 1. -/
noncomputable def GTopOne : 𝟙_ (TopCat.{u}) ⟶ GTop G :=
  TopCat.ofHom ⟨fun _ => 1, continuous_const⟩

/-- The multiplication map of the topological monoid object.

For a monoid G with continuous multiplication, this continuous map G × G → G sends (g,h) to
gh. -/
noncomputable def GTopMul : GTop G ⊗ GTop G ⟶ GTop G :=
  TopCat.ofHom ⟨fun p => p.1 * p.2, continuous_mul⟩

/-- The internal monoid structure in topological spaces.

The usual unit and continuous multiplication of G make its bundled space a monoid object in
the cartesian category TopCat. -/
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

/-- The bundled internal topological monoid.

Bundle G and its internal unit and multiplication as an object of the category of monoid
objects in TopCat. -/
noncomputable abbrev GTopMon : Mon TopCat.{u} where
  X := GTop G

/-- The carrier object of the bundled topological monoid.

The underlying topological object of GTopMon G is GTop G. -/
@[simp]
theorem GTopMon_X : (GTopMon G).X = GTop G :=
  rfl

/-- The cartesian unit topological space.

The space topPoint is the tensor unit of TopCat, hence a one-point space. -/
@[reducible]
def topPoint : TopCat.{u} :=
  𝟙_ (TopCat.{u})

/-- The trivial left point module of a topological monoid.

The cartesian unit space has the unique left action of G, giving a module object over the
internal monoid GTop G. -/
@[instance_reducible]
noncomputable def topPointModObj : ModObj (GTop G) topPoint.{u} :=
  ClassifyingBar.pointModObj (GTopMon G)

attribute [local instance] topPointModObj

/-- The trivial right point action of a topological monoid.

The action topPoint × G → topPoint is the first projection to the point factor. -/
noncomputable def topPointRightAction : topPoint.{u} ⊗ GTop G ⟶ topPoint.{u} :=
  CartesianMonoidalCategory.fst topPoint.{u} (GTop G)

/-- The unit law of the right topological point action.

Insertion of the monoid unit followed by the point action equals the right unitor of topPoint. -/
theorem topPointRightAction_one :
    (topPoint.{u} ◁ MonObj.one (X := GTop G)) ≫ topPointRightAction G =
      (ρ_ topPoint.{u}).hom :=
  ClassifyingBar.pointRightAction_one (GTopMon G)

/-- The associativity law of the right topological point action.

Acting on the point by the product of two monoid elements agrees with acting successively,
with the cartesian associator included. -/
theorem topPointRightAction_assoc :
    (α_ topPoint.{u} (GTop G) (GTop G)).hom ≫
        (topPoint.{u} ◁ MonObj.mul (X := GTop G)) ≫ topPointRightAction G =
      (topPointRightAction G ▷ GTop G) ≫ topPointRightAction G :=
  ClassifyingBar.pointRightAction_assoc (GTopMon G)

/-- The augmentation of a topological monoid to the point.

This is the unique continuous map G → topPoint. -/
noncomputable def topAugmentation : GTop G ⟶ topPoint.{u} :=
  CartesianMonoidalCategory.toUnit (GTop G)

/-- Compatibility of augmentation and the point action.

Augmenting the first factor and then acting on the point agrees with multiplying in G and then
augmenting. -/
theorem topAugmentation_compat :
    (topAugmentation G ▷ GTop G) ≫ topPointRightAction G =
      MonObj.mul (X := GTop G) ≫ topAugmentation G :=
  ClassifyingBar.augmentation_compat (GTopMon G)

/-- The one-point bar evaluation index.

This is the distinguished object of the discrete one-point category used to evaluate the
point-module bar. -/
def topBarIndex : Discrete PUnit.{1} :=
  ClassifyingBar.index

/-- Evaluation of topological point-module diagrams.

Evaluate a functor from the discrete one-point index category to TopCat at its distinguished
point. -/
noncomputable def topBarEvaluation :
    (Discrete PUnit.{1} ⥤ TopCat.{u}) ⥤ TopCat.{u} :=
  ClassifyingBar.pointEvaluation TopCat.{u}

/-- The topological classifying bar of a monoid.

For a topological monoid G with continuous multiplication, this is the two-sided simplicial
bar B(*,G,*) in TopCat. Its degree-n space is homeomorphic to Gⁿ. -/
noncomputable def BBar : SimplicialObject TopCat.{u} :=
  (ClassifyingBar.classifyingBarFunctor TopCat.{u}).obj (GTopMon G)

/-- The topological universal bar of a monoid.

For a topological monoid G with continuous multiplication, this is B(G,G,*) with the regular
right endpoint action. Its degree-n space is homeomorphic to Gⁿ⁺¹. -/
noncomputable def EBar : SimplicialObject TopCat.{u} :=
  (ClassifyingBar.universalBarFunctor TopCat.{u}).obj (GTopMon G)

/-- The map from the universal bar to the classifying bar.

Augment the regular G endpoint to the point in B(G,G,*), giving a simplicial map EBar G → BBar
G. -/
noncomputable def EBarToBBar : EBar G ⟶ BBar G :=
  (ClassifyingBar.universalBundleNatTrans TopCat.{u}).app (GTopMon G)

/-- The universal bar augmented to the point.

Equip EBar G with its canonical simplicial augmentation to the constant one-point space. -/
noncomputable def EBarAugmented : SimplicialObject.Augmented TopCat.{u} :=
  ClassifyingBar.universalBarAugmented (GTopMon G)

/-- The simplicial object of the augmented universal bar.

The left component of EBarAugmented G is EBar G. -/
@[simp]
theorem EBarAugmented_left :
    (EBarAugmented G).left = EBar G :=
  ClassifyingBar.universalBarAugmented_left (GTopMon G)

/-- The augmentation object of the universal bar.

The right component of EBarAugmented G is topPoint. -/
@[simp]
theorem EBarAugmented_right :
    (EBarAugmented G).right = topPoint.{u} :=
  ClassifyingBar.universalBarAugmented_right (GTopMon G)

/-- An extra degeneracy of the augmented universal bar.

The regular-endpoint bar contraction gives extra degeneracy maps for EBar G augmented to the
point. The construction applies to any topological monoid with continuous multiplication. -/
noncomputable def EBarExtraDegeneracy :
    SimplicialObject.Augmented.ExtraDegeneracy (EBarAugmented G) :=
  (BarRegularContraction.extraDegeneracySimplicial
    (leftPointModule (GTop G) topPoint.{u})).map topBarEvaluation

/-- The degree-minus-one extra degeneracy of the universal bar.

The extra-degeneracy map from the augmentation object to degree zero is the evaluated regular-
bar contraction map s′. -/
@[simp]
theorem EBarExtraDegeneracy_s' :
    (EBarExtraDegeneracy G).s' =
      (BarRegularContraction.s'
        (leftPointModule (GTop G) topPoint.{u})).app topBarIndex :=
  rfl

/-- The higher extra degeneracies of the universal bar.

In degree n, the extra-degeneracy map is the evaluation at the bar index of the regular-bar
contraction map sₙ. -/
@[simp]
theorem EBarExtraDegeneracy_s (n : ℕ) :
    (EBarExtraDegeneracy G).s n =
      (BarRegularContraction.s
        (leftPointModule (GTop G) topPoint.{u}) n).app topBarIndex :=
  rfl

/-- A splitting of the universal-bar augmentation.

The extra degeneracy supplies a section of the simplicial augmentation EBar G →
const(topPoint), making that augmentation a split epimorphism. -/
noncomputable def EBarSplitEpi : SplitEpi (EBarAugmented G).hom :=
  (EBarExtraDegeneracy G).splitEpi

/-- The contraction homotopy of the universal bar.

The extra degeneracy gives a simplicial homotopy from the augmentation followed by its section
to the identity map of EBar G. -/
noncomputable def EBarHomotopy :
    SimplicialObject.Homotopy
      ((EBarAugmented G).hom ≫ (EBarExtraDegeneracy G).section_)
      (𝟙 (EBarAugmented G).left) :=
  (EBarExtraDegeneracy G).homotopy

section Functoriality

variable {H : Type u} [TopologicalSpace H] [Monoid H] [ContinuousMul H]

/-- The topological map of a continuous monoid homomorphism.

For a continuous monoid homomorphism φ : G → H, this is its underlying continuous map in
TopCat. -/
noncomputable def GTopMap (phi : ContinuousMonoidHom G H) : GTop G ⟶ GTop H :=
  TopCat.ofHom phi.toContinuousMap

/-- Preservation of the internal monoid operations.

The topological map of φ : G → H preserves the unit and multiplication of their cartesian
internal monoid objects. -/
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

/-- The internal monoid morphism of a continuous homomorphism.

For continuous φ : G → H, bundle its topological map and monoid-operation preservation as a
morphism GTopMon G → GTopMon H. -/
noncomputable def GTopMonMap (phi : ContinuousMonoidHom G H) :
    GTopMon G ⟶ GTopMon H :=
  Mon.ofHom (GTopMap G phi)

/-- The map underlying the internal monoid morphism.

The underlying TopCat morphism of GTopMonMap G φ is GTopMap G φ. -/
@[simp]
theorem GTopMonMap_hom (phi : ContinuousMonoidHom G H) :
    (GTopMonMap G phi).hom = GTopMap G phi :=
  rfl

/-- The internal monoid morphism of the identity homomorphism.

The continuous identity of G induces the identity of GTopMon G. -/
@[simp]
theorem GTopMonMap_id :
    GTopMonMap G (ContinuousMonoidHom.id G) = 𝟙 (GTopMon G) := by
  apply Mon.Hom.ext'
  apply TopCat.hom_ext
  ext x
  rfl

/-- Composition of internal topological monoid morphisms.

For continuous monoid homomorphisms φ : G → H and ψ : H → K, their induced internal monoid
morphisms compose to the morphism induced by ψ ∘ φ. -/
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

/-- The tensor-monad morphism of a continuous monoid homomorphism.

A continuous monoid map φ : G → H gives a morphism of cartesian tensor monads G × − → H × −,
acting by φ on the monoid factor. -/
noncomputable def topTensorMonadHom (phi : ContinuousMonoidHom G H) :
    tensorMonad (GTop G) ⟶ tensorMonad (GTop H) :=
  tensorMonadHom (GTopMonMap G phi)

/-- Coordinates of the tensor-monad morphism.

At a topological space X, the tensor-monad morphism of φ sends (g,x) to (φ(g),x). -/
@[simp]
theorem topTensorMonadHom_app (phi : ContinuousMonoidHom G H)
    (X : TopCat.{u}) (p : G × X) :
    (topTensorMonadHom G phi).app X p = (phi p.1, p.2) :=
  rfl

/-- The tensor-monad morphism of the identity map.

The continuous identity monoid homomorphism induces the identity tensor-monad morphism. -/
@[simp]
theorem topTensorMonadHom_id :
    topTensorMonadHom G (ContinuousMonoidHom.id G) = 𝟙 _ := by
  unfold topTensorMonadHom
  rw [GTopMonMap_id, tensorMonadHom_id]

/-- Composition of topological tensor-monad morphisms.

The tensor-monad morphism of ψ ∘ φ is the composite of the tensor-monad morphisms of φ and ψ. -/
@[simp]
theorem topTensorMonadHom_comp
    {K : Type u} [TopologicalSpace K] [Monoid K] [ContinuousMul K]
    (phi : ContinuousMonoidHom G H) (psi : ContinuousMonoidHom H K) :
    topTensorMonadHom G (psi.comp phi) =
      topTensorMonadHom G phi ≫ topTensorMonadHom H psi := by
  unfold topTensorMonadHom
  rw [← GTopMonMap_comp, tensorMonadHom_comp]

/-- The classifying-bar map of a continuous monoid homomorphism.

For continuous φ : G → H, functoriality of B(*,−,*) gives a simplicial map BBar G → BBar H. -/
noncomputable def BBarMap (phi : ContinuousMonoidHom G H) : BBar G ⟶ BBar H :=
  (ClassifyingBar.classifyingBarFunctor TopCat.{u}).map (GTopMonMap G phi)

/-- The degreewise formula for a classifying-bar map.

In degree n, the classifying-bar map is the identity on the outer point factor tensored with
the n-th power of the tensor-monad morphism induced by φ, evaluated at the point. -/
theorem BBarMap_app_op_mk (phi : ContinuousMonoidHom G H) (n : ℕ) :
    (BBarMap G phi).app (op (SimplexCategory.mk n)) =
      (tensorLeft topPoint.{u}).map
        ((monadPowHom (topTensorMonadHom G phi) n).app topPoint.{u}) :=
  ClassifyingBar.classifyingBarMap_app_op_mk (GTopMonMap G phi) n

/-- The classifying-bar map of an identity homomorphism.

The continuous identity of G induces the identity of BBar G. -/
theorem BBarMap_id :
    BBarMap G (ContinuousMonoidHom.id G) = 𝟙 (BBar G) := by
  unfold BBarMap BBar
  rw [GTopMonMap_id, Functor.map_id]

/-- Composition of topological classifying-bar maps.

For continuous monoid maps φ and ψ, BBarMap φ followed by BBarMap ψ equals BBarMap of ψ ∘ φ. -/
theorem BBarMap_comp
    {K : Type u} [TopologicalSpace K] [Monoid K] [ContinuousMul K]
    (phi : ContinuousMonoidHom G H) (psi : ContinuousMonoidHom H K) :
    BBarMap G phi ≫ BBarMap H psi = BBarMap G (psi.comp phi) := by
  unfold BBarMap BBar
  rw [← Functor.map_comp, GTopMonMap_comp]

/-- The induced map of regular right tensor-monad modules.

For φ : G → H, the regular right module of G × − maps to the regular right module of H × −
restricted along the induced tensor-monad morphism. -/
noncomputable def topRegularRightModuleHom (phi : ContinuousMonoidHom G H) :
    RightModule.regular (tensorMonad (GTop G)) ⟶
      (rightModuleRestrictAlongHom (topTensorMonadHom G phi)).obj
        (RightModule.regular (tensorMonad (GTop H))) :=
  tensorMonadRegularRightModuleHom (GTopMonMap G phi)

/-- The point-module map after monad restriction.

For φ : G → H, the trivial point module for G maps to the trivial point module for H
restricted along the induced tensor-monad morphism. Its underlying point-module map is the
identity. -/
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

/-- The universal-bar map of a continuous monoid homomorphism.

For continuous φ : G → H, functoriality of B(−,−,*) gives a simplicial map EBar G → EBar H. -/
noncomputable def EBarMap (phi : ContinuousMonoidHom G H) : EBar G ⟶ EBar H :=
  (ClassifyingBar.universalBarFunctor TopCat.{u}).map (GTopMonMap G phi)

/-- The degreewise formula for a universal-bar map.

In degree n, first apply φ to the regular outer G-factor, then apply the n-th iterated tensor-
monad map to the remaining factors, as expressed by the tensor-monad component followed by its
action on the power map. -/
theorem EBarMap_app_op_mk (phi : ContinuousMonoidHom G H) (n : ℕ) :
    (EBarMap G phi).app (op (SimplexCategory.mk n)) =
      (topTensorMonadHom G phi).app
          ((monadPow (tensorMonad (GTop G)) n).obj topPoint.{u}) ≫
        (tensorMonad (GTop H)).map
          ((monadPowHom (topTensorMonadHom G phi) n).app topPoint.{u}) :=
  ClassifyingBar.universalBarMap_app_op_mk (GTopMonMap G phi) n

/-- The universal-bar map of an identity homomorphism.

The continuous identity of G induces the identity of EBar G. -/
theorem EBarMap_id :
    EBarMap G (ContinuousMonoidHom.id G) = 𝟙 (EBar G) := by
  unfold EBarMap EBar
  rw [GTopMonMap_id, Functor.map_id]

/-- Composition of topological universal-bar maps.

For continuous monoid maps φ and ψ, EBarMap φ followed by EBarMap ψ equals EBarMap of ψ ∘ φ. -/
theorem EBarMap_comp
    {K : Type u} [TopologicalSpace K] [Monoid K] [ContinuousMul K]
    (phi : ContinuousMonoidHom G H) (psi : ContinuousMonoidHom H K) :
    EBarMap G phi ≫ EBarMap H psi = EBarMap G (psi.comp phi) := by
  unfold EBarMap EBar
  rw [← Functor.map_comp, GTopMonMap_comp]

/-- Naturality of the universal-to-classifying bar map.

For continuous φ : G → H, the square between EBar G → BBar G and EBar H → BBar H commutes with
the induced universal and classifying bar maps. -/
theorem EBarToBBar_naturality (phi : ContinuousMonoidHom G H) :
    EBarMap G phi ≫ EBarToBBar H = EBarToBBar G ≫ BBarMap G phi := by
  change ClassifyingBar.universalBarMap (GTopMonMap G phi) ≫
      ClassifyingBar.universalBundleMap (GTopMon H) =
    ClassifyingBar.universalBundleMap (GTopMon G) ≫
      ClassifyingBar.classifyingBarMap (GTopMonMap G phi)
  exact ClassifyingBar.universalBundle_naturality (GTopMonMap G phi)

/-- The induced map of augmented universal bars.

A continuous monoid homomorphism induces the universal-bar simplicial map on the left and the
identity on the common augmentation point. -/
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

/-- The simplicial component of an augmented bar map.

The left component of EBarAugmentedMap φ is EBarMap φ. -/
@[simp]
theorem EBarAugmentedMap_left (phi : ContinuousMonoidHom G H) :
    (EBarAugmentedMap G phi).left = EBarMap G phi :=
  rfl

/-- The augmentation component of an augmented bar map.

The right component of EBarAugmentedMap φ is the identity of topPoint. -/
@[simp]
theorem EBarAugmentedMap_right (phi : ContinuousMonoidHom G H) :
    (EBarAugmentedMap G phi).right = 𝟙 topPoint.{u} :=
  rfl

/-- Naturality of the universal-bar augmentation.

The universal-bar map induced by φ commutes with the augmentations to the point, whose induced
map is the identity. -/
theorem EBarAugmentation_naturality (phi : ContinuousMonoidHom G H) :
    EBarMap G phi ≫ (EBarAugmented H).hom =
      (EBarAugmented G).hom ≫
        (SimplicialObject.const TopCat.{u}).map (𝟙 topPoint.{u}) :=
  (EBarAugmentedMap G phi).w

end Functoriality

/-- The degree object of the topological classifying bar.

The degree-n object is topPoint × Tⁿ(topPoint), where T = G × − is the topological tensor
monad. -/
@[simp]
theorem BBar_obj (n : ℕ) :
    (BBar G).obj (Opposite.op (SimplexCategory.mk n)) =
      (tensorLeft topPoint.{u}).obj
        ((monadPow (tensorMonad (GTop G)) n).obj topPoint.{u}) :=
  rfl

/-- The degree object of the topological universal bar.

The degree-n object is G × Tⁿ(topPoint), where T = G × − is the topological tensor monad. -/
@[simp]
theorem EBar_obj (n : ℕ) :
    (EBar G).obj (Opposite.op (SimplexCategory.mk n)) =
      (tensorLeft (GTop G)).obj
        ((monadPow (tensorMonad (GTop G)) n).obj topPoint.{u}) :=
  rfl

/-- The homeomorphism appending one tuple coordinate.

For a topological space G, the product Gⁿ × G is homeomorphic to Gⁿ⁺¹ by appending the final
coordinate. -/
noncomputable def topFinSnocHomeomorph (n : ℕ) :
    ((Fin n → G) × G) ≃ₜ (Fin (n + 1) → G) :=
  ((Homeomorph.refl (Fin n → G)).prodCongr
      (Homeomorph.piUnique (fun _ : Fin 1 ↦ G)).symm).trans
    (Fin.appendHomeomorph (X := G) n 1)

/-- The homeomorphism prepending one tuple coordinate.

For a topological space G, the product G × Gⁿ is homeomorphic to Gⁿ⁺¹ by inserting the first
coordinate. -/
noncomputable def topFinConsHomeomorph (n : ℕ) :
    (G × (Fin n → G)) ≃ₜ (Fin (n + 1) → G) where
  toEquiv := Fin.consEquiv (fun _ : Fin (n + 1) ↦ G)
  continuous_toFun := continuous_pi fun i => Fin.cases continuous_fst
    (fun j => (continuous_apply j).comp continuous_snd) i
  continuous_invFun := (continuous_apply (0 : Fin (n + 1))).prodMk
    (continuous_pi fun i : Fin n => continuous_apply i.succ)

/-- Topological tuple coordinates for tensor-monad powers.

For T = G × −, the carrier of Tⁿ(X) is homeomorphic to Gⁿ × X. The equivalence orders monoid
factors from outermost to innermost and retains the X-coordinate. -/
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

/-- The classifying-bar degree homeomorphism.

The degree-n space BBar G is homeomorphic to the finite product Gⁿ, by removing its point
factors and reading the tensor-monad power coordinates. -/
noncomputable def BBarDegreeHomeomorph (n : ℕ) :
    ((BBar G).obj (Opposite.op (SimplexCategory.mk n)) : Type _) ≃ₜ
      (Fin n → G) :=
  (TopCat.homeoOfIso
      (λ_ ((monadPow (tensorMonad (GTop G)) n).obj topPoint.{u}))).trans
    ((topMonadPowTupleHomeomorph (G := G) topPoint.{u} n).trans
      (TopCat.homeoOfIso (ρ_ (TopCat.of (Fin n → G)))))

/-- The universal-bar degree homeomorphism.

The degree-n space EBar G is homeomorphic to Gⁿ⁺¹. The regular outer G-factor is coordinate 0,
followed by the n tensor-monad coordinates. -/
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
/-- Coordinates of the tuple-appending homeomorphism.

The homeomorphism Gⁿ × G → Gⁿ⁺¹ sends (t,g) to Fin.snoc t g. -/
@[simp]
theorem topFinSnocHomeomorph_apply (n : ℕ) (t : Fin n → G) (g : G) :
    topFinSnocHomeomorph (G := G) n (t, g) = Fin.snoc t g := by
  change Fin.append t (fun _ => g) = Fin.snoc t g
  rw [Fin.append_right_eq_snoc]

omit [Monoid G] [ContinuousMul G] in
/-- Coordinates of the tuple-prepending homeomorphism.

The homeomorphism G × Gⁿ → Gⁿ⁺¹ sends (g,t) to Fin.cons g t. -/
@[simp]
theorem topFinConsHomeomorph_apply (n : ℕ) (g : G) (t : Fin n → G) :
    topFinConsHomeomorph (G := G) n (g, t) = Fin.cons g t :=
  rfl

/-- Coordinates at tensor-monad power zero.

The degree-zero tensor-monad power sends x ∈ X to the pair consisting of the empty G-tuple and
x. -/
@[simp]
theorem topMonadPowTupleHomeomorph_zero_apply (X : TopCat.{u}) (x : X) :
    topMonadPowTupleHomeomorph (G := G) X 0 x = (fun i => Fin.elim0 i, x) :=
  rfl

/-- The successor formula for topological power coordinates.

Read Tⁿ⁺¹(X) first through the level-n homeomorphism at TX. If the result is (t,(g,x)), its
level-(n+1) coordinates are (Fin.snoc t g,x). -/
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
/-- Values of the topological monoid unit map.

Every point of the cartesian unit is sent to 1 ∈ G. -/
@[simp]
theorem GTopOne_apply (p : (𝟙_ (TopCat.{u}) : Type _)) :
    GTopOne G p = 1 :=
  rfl

/-- Values of the topological monoid multiplication map.

The multiplication map sends (g,h) to gh. -/
@[simp]
theorem GTopMul_apply (p : G × G) :
    GTopMul G p = p.1 * p.2 :=
  rfl

omit [Monoid G] [ContinuousMul G] in
/-- Values of the right point action.

The action topPoint × G → topPoint sends a pair to its first component. -/
@[simp]
theorem topPointRightAction_apply (p : (topPoint.{u} ⊗ GTop G : TopCat.{u})) :
    topPointRightAction G p = p.1 :=
  rfl

omit [Monoid G] [ContinuousMul G] in
/-- Values of the topological monoid augmentation.

The augmentation sends every g ∈ G to the unique point. -/
@[simp]
theorem topAugmentation_apply (g : G) :
    topAugmentation G g = PUnit.unit :=
  rfl

/-- Naturality of topological power coordinates in the base space.

For a continuous map f : X → Y, the map Tⁿ(f) preserves the G-tuple and applies f to the final
base coordinate. -/
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

/-- Coordinates of a classifying-bar element.

Read the inner tensor-monad power factor of a degree-n classifying-bar element and take its
G-tuple, discarding the point coordinate. -/
@[simp]
theorem BBarDegreeHomeomorph_apply (n : ℕ)
    (x : ((BBar G).obj (Opposite.op (SimplexCategory.mk n)) : Type _)) :
    BBarDegreeHomeomorph G n x =
      (topMonadPowTupleHomeomorph (G := G) topPoint.{u} n x.2).1 :=
  rfl

/-- Coordinates of a universal-bar element.

For a degree-n universal-bar element (g,y), prepend the regular coordinate g to the G-tuple
read from y. -/
@[simp]
theorem EBarDegreeHomeomorph_apply (n : ℕ)
    (x : ((EBar G).obj (Opposite.op (SimplexCategory.mk n)) : Type _)) :
    EBarDegreeHomeomorph G n x =
      Fin.cons x.1
        (topMonadPowTupleHomeomorph (G := G) topPoint.{u} n x.2).1 :=
  rfl

/-- Removal of a finite tuple coordinate.

For i : Fin (n+1), remove entry i from a tuple of length n+1 to obtain a tuple of length n. -/
def topTupleRemove {n : ℕ} (i : Fin (n + 1)) (t : Fin (n + 1) → G) :
    Fin n → G :=
  Fin.removeNth i t

/-- Contraction of adjacent topological monoid coordinates.

For i : Fin n, replace entries i and i+1 of a tuple of length n+1 by their ordered product,
producing a tuple of length n. -/
def topTupleContract {n : ℕ} (i : Fin n) (t : Fin (n + 1) → G) :
    Fin n → G :=
  Fin.contractNth i.castSucc (fun x y => x * y) t

/-- Insertion of a monoid unit into a finite tuple.

For i : Fin (n+1), insert 1 at position i of a tuple of length n. -/
def topTupleInsert {n : ℕ} (i : Fin (n + 1)) (t : Fin n → G) :
    Fin (n + 1) → G :=
  Fin.insertNth i 1 t

/-- Coordinates of the topological tensor-monad unit.

The unit at X sends x to (1,x) in G × X. -/
@[simp]
theorem topTensorMonad_eta_apply (X : TopCat.{u}) (x : X) :
    (tensorMonad (GTop G)).η.app X x = (1, x) :=
  rfl

/-- Coordinates of the topological tensor-monad multiplication.

The multiplication at X sends (g,(h,x)) to (gh,x). -/
@[simp]
theorem topTensorMonad_mu_apply (X : TopCat.{u})
    (p : G × G × X) :
    (tensorMonad (GTop G)).μ.app X p = (p.1 * p.2.1, p.2.2) :=
  rfl

omit [TopologicalSpace G] [ContinuousMul G] in
/-- Adjacent contraction before an appended coordinate.

Contracting at the inherited index i in Fin.snoc t g equals appending g after contracting t at
i. -/
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
/-- Adjacent contraction after a prepended coordinate.

Contracting Fin.cons g t at index i+1 equals prepending g to the contraction of t at i. -/
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

/-- Power coordinates of monad multiplication at a position.

For j : Fin n, multiplying at monad position j contracts tuple entries at index n−1−j and
retains the base coordinate. The reversed index reflects the monad-position convention. -/
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

/-- Power coordinates of bar multiplication at a position.

The bar multiplication at index j contracts tuple entries j and j+1 in their displayed order
and retains the base coordinate. -/
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
/-- Unit insertion before an appended coordinate.

Inserting 1 into Fin.snoc t g at the inherited index i equals appending g after inserting 1
into t at i. -/
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

/-- Power coordinates of monad unit insertion at a position.

For j : Fin (n+1), insertion at monad position j inserts 1 into the tuple at index n−j and
retains the base coordinate. -/
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

/-- Power coordinates of bar unit insertion at a position.

The bar unit insertion at index j inserts 1 at tuple position j and retains the base
coordinate. -/
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
/-- Unit insertion after a prepended coordinate.

Inserting 1 into Fin.cons g t at position i+1 equals prepending g to the insertion into t at
i. -/
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

/-- The tuple remaining after a map on the innermost pair.

For a continuous map f : TX → Y, the tuple component of Tⁿ(f) on Tⁿ⁺¹(X) is the initial n
entries of the source tuple. -/
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

/-- The classifying-bar degree isomorphism in topological spaces.

The degree-n object of BBar G is isomorphic in TopCat to the finite product space Gⁿ via its
degree homeomorphism. -/
noncomputable def BBarDegreeIso (n : ℕ) :
    (BBar G).obj (Opposite.op (SimplexCategory.mk n)) ≅
      TopCat.of (Fin n → G) :=
  TopCat.isoOfHomeo (BBarDegreeHomeomorph G n)

/-- The universal-bar degree isomorphism in topological spaces.

The degree-n object of EBar G is isomorphic in TopCat to the finite product space Gⁿ⁺¹ via its
degree homeomorphism. -/
noncomputable def EBarDegreeIso (n : ℕ) :
    (EBar G).obj (Opposite.op (SimplexCategory.mk n)) ≅
      TopCat.of (Fin (n + 1) → G) :=
  TopCat.isoOfHomeo (EBarDegreeHomeomorph G n)

/-- The initial face of the topological classifying bar.

The zeroth face is the evaluated two-sided bar face using the trivial right point action and
trivial left point module. -/
theorem BBar_d0 (n : ℕ) :
    (BBar G).map (SimplexCategory.δ (0 : Fin (n + 2))).op =
      barFaceApp
        (R := rightModuleOfRightAction topPoint.{u} (GTop G)
          (topPointRightAction G) (topPointRightAction_one G)
          (topPointRightAction_assoc G))
        (L := leftPointModule (GTop G) topPoint.{u}) n 0 topBarIndex := by
  exact classifyingBar_d0 (GTop G) topPoint.{u} (topPointRightAction G)
    (topPointRightAction_one G) (topPointRightAction_assoc G) n topBarIndex

/-- The terminal face of the topological classifying bar.

The last face is the evaluated two-sided bar face using the trivial left point module at the
terminal endpoint. -/
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

/-- Interior faces of the topological classifying bar.

For k : Fin n, the face at k+1 is the bar multiplication at position k, tensored on the left
with the outer point factor. -/
theorem BBar_dInterior (n : ℕ) (k : Fin n) :
    (BBar G).map (SimplexCategory.δ (k.succ.castSucc : Fin (n + 2))).op =
      (tensorLeft topPoint.{u}).map
        (barMuAtPos (tensorMonad (GTop G)) n k
          ((leftPointModule (GTop G) topPoint.{u}).functor.obj topBarIndex)) := by
  exact classifyingBar_dInterior (GTop G) topPoint.{u} (topPointRightAction G)
    (topPointRightAction_one G) (topPointRightAction_assoc G) n k topBarIndex

/-- Degeneracies of the topological classifying bar.

The degeneracy at i is the bar unit insertion at position i, tensored on the left with the
point factor. -/
theorem BBar_s (n : ℕ) (i : Fin (n + 1)) :
    (BBar G).map (SimplexCategory.σ i).op =
      (tensorLeft topPoint.{u}).map
        (barEtaAtPos (tensorMonad (GTop G)) n i topPoint.{u}) := by
  exact classifyingBar_s (GTop G) topPoint.{u} (topPointRightAction G)
    (topPointRightAction_one G) (topPointRightAction_assoc G) n i topBarIndex

/-- The initial face of the topological universal bar.

The zeroth face is the evaluated two-sided bar face using multiplication as the regular right
endpoint action of G. -/
theorem EBar_d0 (n : ℕ) :
    (EBar G).map (SimplexCategory.δ (0 : Fin (n + 2))).op =
      barFaceApp
        (R := rightModuleOfRightAction (GTop G) (GTop G) MonObj.mul
          (MonObj.mul_one (GTop G)) ((MonObj.mul_assoc (GTop G)).symm))
        (L := leftPointModule (GTop G) topPoint.{u}) n 0 topBarIndex := by
  exact universalBar_d0 (GTop G) topPoint.{u} n topBarIndex

/-- The terminal face of the topological universal bar.

The last face is the evaluated two-sided bar face using the trivial left point module at the
terminal endpoint. -/
theorem EBar_dLast (n : ℕ) :
    (EBar G).map (SimplexCategory.δ (Fin.last (n + 1))).op =
      barFaceApp
        (R := rightModuleOfRightAction (GTop G) (GTop G) MonObj.mul
          (MonObj.mul_one (GTop G)) ((MonObj.mul_assoc (GTop G)).symm))
        (L := leftPointModule (GTop G) topPoint.{u}) n (Fin.last (n + 1))
          topBarIndex := by
  exact universalBar_dLast (GTop G) topPoint.{u} n topBarIndex

/-- Interior faces of the topological universal bar.

For k : Fin n, the face at k+1 is the bar multiplication at position k, tensored on the left
with the regular outer G-factor. -/
theorem EBar_dInterior (n : ℕ) (k : Fin n) :
    (EBar G).map (SimplexCategory.δ (k.succ.castSucc : Fin (n + 2))).op =
      (tensorLeft (GTop G)).map
        (barMuAtPos (tensorMonad (GTop G)) n k
          ((leftPointModule (GTop G) topPoint.{u}).functor.obj topBarIndex)) := by
  exact universalBar_dInterior (GTop G) topPoint.{u} n k topBarIndex

/-- Degeneracies of the topological universal bar.

The degeneracy at i is the bar unit insertion at position i in the inner power, tensored on
the left with the regular G-factor. -/
theorem EBar_s (n : ℕ) (i : Fin (n + 1)) :
    (EBar G).map (SimplexCategory.σ i).op =
      (tensorLeft (GTop G)).map
        (barEtaAtPos (tensorMonad (GTop G)) n i topPoint.{u}) := by
  exact universalBar_s (GTop G) topPoint.{u} n i topBarIndex

/-- Components of the universal-to-classifying bar map.

Each component is the evaluation of the canonical two-sided bar map obtained by augmenting the
regular outer G-factor to the point. -/
@[simp]
theorem EBarToBBar_app (Δ : SimplexCategoryᵒᵖ) :
    (EBarToBBar G).app Δ = topBarEvaluation.map
      ((universalBundle (GTop G) topPoint.{u} (topPointRightAction G)
        (topPointRightAction_one G) (topPointRightAction_assoc G)
        (topAugmentation G) (topAugmentation_compat G)).app Δ) :=
  rfl

/-- The initial classifying-bar face in tuple coordinates.

For t of length n+1, the zeroth face has tuple Fin.tail t, removing the first entry. -/
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

/-- The initial classifying-bar face as coordinate removal.

Under the degree homeomorphisms, d₀ removes tuple coordinate 0. -/
theorem BBarDegreeHomeomorph_d0_remove (n : ℕ)
    (x : ((BBar G).obj (Opposite.op (SimplexCategory.mk (n + 1))) : Type _)) :
    BBarDegreeHomeomorph G n
        ((BBar G).map (SimplexCategory.δ (0 : Fin (n + 2))).op x) =
      topTupleRemove G 0 (BBarDegreeHomeomorph G (n + 1) x) := by
  rw [topTupleRemove, Fin.removeNth_zero]
  exact BBarDegreeHomeomorph_d0 G n x

/-- The terminal classifying-bar face in tuple coordinates.

For t of length n+1, the last face has tuple Fin.init t, removing the last entry. -/
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

/-- The terminal classifying-bar face as coordinate removal.

Under the degree homeomorphisms, the last face removes index Fin.last n from the source tuple
of length n+1. -/
theorem BBarDegreeHomeomorph_dLast_remove (n : ℕ)
    (x : ((BBar G).obj (Opposite.op (SimplexCategory.mk (n + 1))) : Type _)) :
    BBarDegreeHomeomorph G n
        ((BBar G).map (SimplexCategory.δ (Fin.last (n + 1))).op x) =
      topTupleRemove G (Fin.last n) (BBarDegreeHomeomorph G (n + 1) x) := by
  rw [topTupleRemove, Fin.removeNth_last]
  exact BBarDegreeHomeomorph_dLast G n x

/-- An interior classifying-bar face in tuple coordinates.

The face at k+1 contracts entries k and k+1 by their product gₖgₖ₊₁, with the remaining
entries in their original order. -/
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

/-- A classifying-bar degeneracy in tuple coordinates.

The degeneracy at i inserts the monoid identity at tuple position i. -/
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

/-- The initial universal-bar face in tuple coordinates.

For the universal-bar tuple of length n+2, the zeroth face multiplies entries 0 and 1 in that
order. -/
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

/-- An interior universal-bar face in tuple coordinates.

The face at k+1 contracts universal-bar tuple entries k+1 and k+2, retaining the regular
leading coordinate. -/
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

/-- The terminal universal-bar face in tuple coordinates.

The last face removes the final coordinate from the universal-bar tuple by Fin.init. -/
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

/-- The terminal universal-bar face as coordinate removal.

The last face removes index Fin.last (n+1) from the source universal-bar tuple of length n+2. -/
theorem EBarDegreeHomeomorph_dLast_remove (n : ℕ)
    (x : ((EBar G).obj (Opposite.op (SimplexCategory.mk (n + 1))) : Type _)) :
    EBarDegreeHomeomorph G n
        ((EBar G).map (SimplexCategory.δ (Fin.last (n + 1))).op x) =
      topTupleRemove G (Fin.last (n + 1))
        (EBarDegreeHomeomorph G (n + 1) x) := by
  rw [topTupleRemove, Fin.removeNth_last]
  exact EBarDegreeHomeomorph_dLast G n x

/-- A universal-bar degeneracy in tuple coordinates.

The degeneracy at i inserts the monoid identity at position i+1 of the universal-bar tuple,
after its regular leading coordinate. -/
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

/-- The tuple formula for every universal-bar face.

For a tuple of length n+2, d₀ contracts entries 0 and 1, every interior dᵢ contracts entries i
and i+1, and dₙ₊₁ removes the final entry. This is the complete case formula for i : Fin
(n+2). -/
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
