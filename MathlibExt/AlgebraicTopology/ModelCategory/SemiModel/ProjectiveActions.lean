/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction
public import Mathlib.CategoryTheory.LiftingProperties.Limits
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Quot

/-!
# Projective action restriction along injective group homomorphisms

The projective classes are the lifting classes against the underlying
(trivial) fibrations. For groups `H` and `G` and a homomorphism `φ : H →* G`,
coinduction of an `H`-action `X` uses the product of `X.V` indexed by `G`,
the product indexed by `H × G`, and the equalizer of the two maps
expressing the `H`-equivariance equality
`coinductionCoordinate φ X (φ h * g) =
  coinductionCoordinate φ X g ≫ (X.ρ h).asHom`.
Thus the construction assumes products of both shapes and equalizers in
`C`. If `φ` is injective, a split reads the input
coordinates at chosen right-coset representatives and reconstructs the
other coordinates by the `H`-action. The coinduction carrier is a natural
retract of the full product; restriction then preserves the projective
classes. The split does not preserve arbitrary input coordinates at every
`g : G`.

This is White–Yau, *Bousfield localization and algebras over colored operads*,
arXiv:1503.06720v2, Lemma 5.4.1, in the single-object groupoid case.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v uH uG

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.SemiModel.ProjectiveActions

section Classes

variable (C : Type u) [Category.{v} C] [ModelCategory C] (G : Type uG) [Group G]

/-- Projective action cofibrations lift against all underlying trivial fibrations. -/
def projectiveCofibrations : MorphismProperty (Action C G) :=
  ((trivialFibrations C).inverseImage (Action.forget C G)).llp

/-- Projective trivial action cofibrations lift against all underlying fibrations. -/
def projectiveTrivialCofibrations : MorphismProperty (Action C G) :=
  ((fibrations C).inverseImage (Action.forget C G)).llp

/-- Projective cofibrancy uses the actual initial action map. -/
def projectiveCofibrantObject (X : Action C G) : Prop :=
  projectiveCofibrations C G (initial.to X)

end Classes

variable {C : Type u} [Category.{v} C]
  {H : Type uH} [Group H] {G : Type uG} [Group G]
  (φ : H →* G)
  [HasProductsOfShape G C] [HasProductsOfShape (H × G) C] [HasEqualizers C]

/-- The full product used by coinduction. -/
abbrev coinductionProduct (X : Action C H) : C := ∏ᶜ fun _ : G => X.V

/-- Left multiplication on indices supplies the first equivariance map. -/
def coinductionRelationLeft (X : Action C H) :
    coinductionProduct (G := G) X ⟶ ∏ᶜ fun _ : H × G => X.V :=
  Pi.lift (fun hg => Pi.π (fun _ : G => X.V) (φ hg.1 * hg.2))

/-- The original H-action supplies the second equivariance map. -/
def coinductionRelationRight (X : Action C H) :
    coinductionProduct (G := G) X ⟶ ∏ᶜ fun _ : H × G => X.V :=
  Pi.lift (fun hg => Pi.π (fun _ : G => X.V) hg.2 ≫ (X.ρ hg.1).asHom)

omit [HasEqualizers C] in
/-- Projection of the left equivariance map is the original translated coordinate. -/
@[reassoc (attr := simp)]
theorem coinductionRelationLeft_projection (X : Action C H) (h : H) (g : G) :
    coinductionRelationLeft φ X ≫ Pi.π (fun _ : H × G => X.V) (h, g) =
      Pi.π (fun _ : G => X.V) (φ h * g) :=
  Pi.lift_comp_π _ _

omit [Group G] [HasEqualizers C] in
/-- Projection of the right equivariance map is the original action on the coordinate. -/
@[reassoc (attr := simp)]
theorem coinductionRelationRight_projection (X : Action C H) (h : H) (g : G) :
    coinductionRelationRight (G := G) X ≫ Pi.π (fun _ : H × G => X.V) (h, g) =
      Pi.π (fun _ : G => X.V) g ≫ (X.ρ h).asHom :=
  Pi.lift_comp_π _ _

/-- The actual object of equivariant product coordinates. -/
abbrev coinductionCarrier (X : Action C H) : C :=
  equalizer (coinductionRelationLeft φ X) (coinductionRelationRight X)

/-- Each actual product coordinate of the equivariance equalizer. -/
def coinductionCoordinate (X : Action C H) (g : G) : coinductionCarrier φ X ⟶ X.V :=
  equalizer.ι _ _ ≫ Pi.π (fun _ : G => X.V) g

/-- The equalizer retains precisely the original H-equivariance equation. -/
@[reassoc]
theorem coinductionCoordinate_relation (X : Action C H) (h : H) (g : G) :
    coinductionCoordinate φ X (φ h * g) =
      coinductionCoordinate φ X g ≫ (X.ρ h).asHom := by
  have he := congrArg (fun k => k ≫ Pi.π (fun _ : H × G => X.V) (h, g))
    (equalizer.condition (coinductionRelationLeft φ X) (coinductionRelationRight X))
  rw [Category.assoc, coinductionRelationLeft_projection,
    Category.assoc, coinductionRelationRight_projection] at he
  simpa only [coinductionCoordinate, Category.assoc] using he

/-- Right multiplication on the actual coordinates preserves H-equivariance. -/
def coinductionShift (X : Action C H) (k : G) :
    coinductionCarrier φ X ⟶ coinductionCarrier φ X :=
  equalizer.lift (Pi.lift (fun g => coinductionCoordinate φ X (g * k))) (by
    apply Pi.hom_ext
    rintro ⟨h, g⟩
    simp only [Category.assoc, coinductionRelationLeft_projection,
      coinductionRelationRight_projection, Pi.lift_comp_π, Pi.lift_comp_π_assoc]
    simpa only [mul_assoc] using coinductionCoordinate_relation φ X h (g * k))

/-- The shift keeps the complete original coordinate map. -/
@[reassoc (attr := simp)]
theorem coinductionShift_coordinate (X : Action C H) (k g : G) :
    coinductionShift φ X k ≫ coinductionCoordinate φ X g =
      coinductionCoordinate φ X (g * k) := by
  change coinductionShift φ X k ≫ equalizer.ι _ _ ≫ Pi.π (fun _ : G => X.V) g = _
  rw [← Category.assoc, coinductionShift, equalizer.lift_ι, Pi.lift_comp_π]

/-- The actual coinduced G-action. -/
def coinductionAction (X : Action C H) : Action C G where
  V := coinductionCarrier φ X
  ρ :=
    { toFun := fun k => End.of (coinductionShift φ X k)
      map_one' := by
        apply End.ext
        change coinductionShift φ X 1 = 𝟙 _
        apply equalizer.hom_ext
        apply Pi.hom_ext
        intro g
        simpa [coinductionCoordinate, Category.assoc] using
          coinductionShift_coordinate φ X 1 g
      map_mul' := by
        intro k l
        apply End.ext
        change coinductionShift φ X (k * l) = coinductionShift φ X l ≫ coinductionShift φ X k
        apply equalizer.hom_ext
        apply Pi.hom_ext
        intro g
        simp only [Category.assoc]
        change coinductionShift φ X (k * l) ≫ coinductionCoordinate φ X g =
          coinductionShift φ X l ≫ coinductionShift φ X k ≫ coinductionCoordinate φ X g
        simp [mul_assoc] }

/-- The coinduced action has the actual right-shift carrier map. -/
@[simp]
theorem coinductionAction_ρ_hom (X : Action C H) (k : G) :
    ((coinductionAction φ X).ρ k).asHom = coinductionShift φ X k := rfl

/-- The actual map on coinduced carriers. -/
def coinductionMap {X Y : Action C H} (f : X ⟶ Y) :
    coinductionCarrier φ X ⟶ coinductionCarrier φ Y :=
  equalizer.lift (Pi.lift (fun g => coinductionCoordinate φ X g ≫ f.hom)) (by
    apply Pi.hom_ext
    rintro ⟨h, g⟩
    simp only [Category.assoc, coinductionRelationLeft_projection,
      coinductionRelationRight_projection, Pi.lift_comp_π, Pi.lift_comp_π_assoc]
    rw [coinductionCoordinate_relation, Category.assoc, f.comm])

/-- Coinduction retains each original source coordinate and carrier map. -/
@[reassoc (attr := simp)]
theorem coinductionMap_coordinate {X Y : Action C H} (f : X ⟶ Y) (g : G) :
    coinductionMap φ f ≫ coinductionCoordinate φ Y g =
      coinductionCoordinate φ X g ≫ f.hom := by
  change coinductionMap φ f ≫ equalizer.ι _ _ ≫ Pi.π (fun _ : G => Y.V) g = _
  rw [← Category.assoc, coinductionMap, equalizer.lift_ι, Pi.lift_comp_π]

set_option backward.isDefEq.respectTransparency false in
/-- The coinduced carrier maps commute with the full original G-action. -/
def coinductionActionMap {X Y : Action C H} (f : X ⟶ Y) :
    coinductionAction φ X ⟶ coinductionAction φ Y where
  hom := coinductionMap φ f
  comm k := by
    apply equalizer.hom_ext
    apply Pi.hom_ext
    intro g
    have h : coinductionShift φ X k ≫ coinductionMap φ f ≫ coinductionCoordinate φ Y g =
        coinductionMap φ f ≫ coinductionShift φ Y k ≫ coinductionCoordinate φ Y g := by
      simp only [coinductionMap_coordinate, coinductionShift_coordinate,
        coinductionShift_coordinate_assoc]
    simpa only [coinductionAction_ρ_hom, coinductionCoordinate, Category.assoc] using h

/-- The actual carrier of a coinduced action map. -/
@[simp]
theorem coinductionActionMap_hom {X Y : Action C H} (f : X ⟶ Y) :
    (coinductionActionMap φ f).hom = coinductionMap φ f := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual coinduction functor; its action and every map were constructed above. -/
def coinduction : Action C H ⥤ Action C G where
  obj := coinductionAction φ
  map := coinductionActionMap φ
  map_id X := by
    apply Action.Hom.ext
    apply equalizer.hom_ext
    apply Pi.hom_ext
    intro g
    simpa only [coinductionActionMap_hom, coinductionCoordinate, Action.id_hom,
      Category.id_comp, Category.comp_id, Category.assoc] using
      coinductionMap_coordinate φ (𝟙 X) g
  map_comp f g := by
    apply Action.Hom.ext
    apply equalizer.hom_ext
    apply Pi.hom_ext
    intro k
    have h : coinductionMap φ (f ≫ g) ≫ coinductionCoordinate φ _ k =
        coinductionMap φ f ≫ coinductionMap φ g ≫ coinductionCoordinate φ _ k := by
      simp only [coinductionMap_coordinate, coinductionMap_coordinate_assoc, Action.comp_hom]
    simpa only [coinductionActionMap_hom, coinductionCoordinate, Action.comp_hom, Category.assoc]
      using h


set_option backward.isDefEq.respectTransparency false in
/-- Transpose an actual restricted-action map into the coinduced carrier. -/
def coinductionLift {A : Action C G} {X : Action C H}
    (u : (Action.res C φ).obj A ⟶ X) : A.V ⟶ coinductionCarrier φ X :=
  equalizer.lift (Pi.lift (fun g => (A.ρ g).asHom ≫ u.hom)) (by
    apply Pi.hom_ext
    rintro ⟨h, g⟩
    simp only [Category.assoc, coinductionRelationLeft_projection,
      coinductionRelationRight_projection, Pi.lift_comp_π, Pi.lift_comp_π_assoc]
    rw [map_mul, End.mul_asHom, Category.assoc]
    exact congrArg (fun z => (A.ρ g).asHom ≫ z) (u.comm h))

set_option backward.isDefEq.respectTransparency false in
/-- Transposition retains every original input-action coordinate. -/
@[reassoc (attr := simp)]
theorem coinductionLift_coordinate {A : Action C G} {X : Action C H}
    (u : (Action.res C φ).obj A ⟶ X) (g : G) :
    coinductionLift φ u ≫ coinductionCoordinate φ X g = (A.ρ g).asHom ≫ u.hom := by
  change coinductionLift φ u ≫ equalizer.ι _ _ ≫ Pi.π (fun _ : G => X.V) g = _
  rw [← Category.assoc, coinductionLift, equalizer.lift_ι, Pi.lift_comp_π]

set_option backward.isDefEq.respectTransparency false in
/-- The original transpose is equivariant for the complete G-action. -/
def coinductionLiftAction {A : Action C G} {X : Action C H}
    (u : (Action.res C φ).obj A ⟶ X) : A ⟶ coinductionAction φ X where
  hom := coinductionLift φ u
  comm k := by
    apply equalizer.hom_ext
    apply Pi.hom_ext
    intro g
    have h : (A.ρ k).asHom ≫ coinductionLift φ u ≫ coinductionCoordinate φ X g =
        coinductionLift φ u ≫ coinductionShift φ X k ≫ coinductionCoordinate φ X g := by
      rw [coinductionLift_coordinate, coinductionShift_coordinate, coinductionLift_coordinate]
      simp only [map_mul, End.mul_asHom, Category.assoc]
    simpa only [coinductionCoordinate, coinductionAction_ρ_hom, Category.assoc] using h

set_option backward.isDefEq.respectTransparency false in
/-- Evaluate the actual coinduced coordinates at the group identity. -/
def coinductionEvaluate {A : Action C G} {X : Action C H}
    (v : A ⟶ coinductionAction φ X) : (Action.res C φ).obj A ⟶ X where
  hom := v.hom ≫ coinductionCoordinate φ X 1
  comm h := by
    change (A.ρ (φ h)).asHom ≫ (v.hom ≫ coinductionCoordinate φ X 1) =
      (v.hom ≫ coinductionCoordinate φ X 1) ≫ (X.ρ h).asHom
    rw [← Category.assoc, v.comm, Category.assoc, coinductionAction_ρ_hom,
      coinductionShift_coordinate, one_mul]
    rw [← mul_one (φ h), coinductionCoordinate_relation]
    simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation after transposition is the entire original H-action morphism. -/
theorem coinductionEvaluate_lift {A : Action C G} {X : Action C H}
    (u : (Action.res C φ).obj A ⟶ X) :
    coinductionEvaluate φ (coinductionLiftAction φ u) = u := by
  apply Action.Hom.ext
  change coinductionLift φ u ≫ coinductionCoordinate φ X 1 = u.hom
  rw [coinductionLift_coordinate]
  simp only [map_one, End.one_asHom, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Transposition after evaluation retains every complete coinduced coordinate. -/
theorem coinductionLift_evaluate {A : Action C G} {X : Action C H}
    (v : A ⟶ coinductionAction φ X) :
    coinductionLiftAction φ (coinductionEvaluate φ v) = v := by
  apply Action.Hom.ext
  apply equalizer.hom_ext
  apply Pi.hom_ext
  intro g
  have h : coinductionLift φ (coinductionEvaluate φ v) ≫ coinductionCoordinate φ X g =
      v.hom ≫ coinductionCoordinate φ X g := by
    rw [coinductionLift_coordinate]
    change (A.ρ g).asHom ≫ (v.hom ≫ coinductionCoordinate φ X 1) = _
    rw [← Category.assoc, v.comm, Category.assoc, coinductionAction_ρ_hom,
      coinductionShift_coordinate, one_mul]
  simpa only [coinductionLiftAction, coinductionCoordinate, Category.assoc] using h

set_option backward.isDefEq.respectTransparency false in
/-- The genuine restriction/coinduction Hom equivalence. -/
def coinductionHomEquiv (A : Action C G) (X : Action C H) :
    ((Action.res C φ).obj A ⟶ X) ≃ (A ⟶ coinductionAction φ X) where
  toFun := coinductionLiftAction φ
  invFun := coinductionEvaluate φ
  left_inv := coinductionEvaluate_lift φ
  right_inv := coinductionLift_evaluate φ

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation is natural in the original G-action source map. -/
theorem coinductionEvaluate_naturality_left {A B : Action C G} {X : Action C H}
    (a : A ⟶ B) (v : B ⟶ coinductionAction φ X) :
    coinductionEvaluate φ (a ≫ v) =
      (Action.res C φ).map a ≫ coinductionEvaluate φ v := by
  apply Action.Hom.ext
  simp only [coinductionEvaluate, Action.comp_hom, Action.res_map_hom, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Transposition is natural in the original H-action target map. -/
theorem coinductionLift_naturality_right {A : Action C G} {X Y : Action C H}
    (u : (Action.res C φ).obj A ⟶ X) (f : X ⟶ Y) :
    coinductionLiftAction φ (u ≫ f) =
      coinductionLiftAction φ u ≫ (coinduction φ).map f := by
  apply Action.Hom.ext
  apply equalizer.hom_ext
  apply Pi.hom_ext
  intro g
  have h : coinductionLift φ (u ≫ f) ≫ coinductionCoordinate φ Y g =
      coinductionLift φ u ≫ coinductionMap φ f ≫ coinductionCoordinate φ Y g := by
    simp only [coinductionLift_coordinate, coinductionMap_coordinate,
      coinductionLift_coordinate_assoc, Action.comp_hom]
  simpa only [coinductionLiftAction, coinduction, coinductionActionMap_hom,
    coinductionCoordinate, Action.comp_hom, Category.assoc] using h

/-- Restriction is left adjoint to the genuinely constructed coinduction functor. -/
def restrictionCoinductionAdjunction : Action.res C φ ⊣ coinduction φ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := coinductionHomEquiv φ
      homEquiv_naturality_left_symm := coinductionEvaluate_naturality_left φ
      homEquiv_naturality_right := coinductionLift_naturality_right φ }

/-- The selected representative of the actual right coset of g. -/
def cosetRepresentative (g : G) : G :=
  (Quotient.mk (QuotientGroup.rightRel φ.range) g).out

/-- The representative is in the actual H-orbit of the original group element. -/
theorem cosetRepresentative_related (g : G) :
    g * (cosetRepresentative φ g)⁻¹ ∈ φ.range := by
  exact QuotientGroup.rightRel_apply.mp
    (Quotient.exact (Quotient.out_eq
      (Quotient.mk (QuotientGroup.rightRel φ.range) g)))

/-- The H-coordinate of each element relative to its actual selected coset representative. -/
def cosetCoordinate (g : G) : H :=
  (MonoidHom.mem_range.mp (cosetRepresentative_related φ g)).choose

/-- The chosen coordinate gives the original whole group element, not only its coset. -/
theorem cosetCoordinate_factor (g : G) :
    φ (cosetCoordinate φ g) * cosetRepresentative φ g = g := by
  have h := (MonoidHom.mem_range.mp (cosetRepresentative_related φ g)).choose_spec
  change φ (cosetCoordinate φ g) = g * (cosetRepresentative φ g)⁻¹ at h
  rw [h]
  simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- H-translation keeps the actual chosen orbit representative. -/
theorem cosetRepresentative_translate (h : H) (g : G) :
    cosetRepresentative φ (φ h * g) = cosetRepresentative φ g := by
  have he : Quotient.mk (QuotientGroup.rightRel φ.range) g =
      Quotient.mk (QuotientGroup.rightRel φ.range) (φ h * g) := by
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using
      (show φ h ∈ φ.range from ⟨h, rfl⟩)
  exact congrArg Quotient.out he.symm

/-- Injectivity makes the original H-transport unique and compatible with translation. -/
theorem cosetCoordinate_translate (hφ : Function.Injective φ) (h : H) (g : G) :
    cosetCoordinate φ (φ h * g) = h * cosetCoordinate φ g := by
  apply hφ
  apply mul_right_cancel (b := cosetRepresentative φ g)
  calc
    φ (cosetCoordinate φ (φ h * g)) * cosetRepresentative φ g =
        φ h * g := by
      rw [← cosetRepresentative_translate φ h g, cosetCoordinate_factor]
    _ = φ (h * cosetCoordinate φ g) * cosetRepresentative φ g := by
      rw [map_mul, mul_assoc, cosetCoordinate_factor]

set_option backward.isDefEq.respectTransparency false in
/-- Let `C` have products indexed by `G` and `H × G` and have equalizers.
For an injective homomorphism `φ : H →* G` and an `H`-action `X`, this map
from the full `G`-indexed product to `coinductionCarrier φ X` reads the
input at `cosetRepresentative φ g` and applies
`(X.ρ (cosetCoordinate φ g)).asHom` to construct its coordinate at `g`.
The equation `φ (cosetCoordinate φ g) * cosetRepresentative φ g = g`
identifies the chosen representative and transport. Arbitrary coordinates
at nonrepresentative indices are reconstructed, not retained unchanged. -/
def coinductionSplit (hφ : Function.Injective φ) (X : Action C H) :
    coinductionProduct (G := G) X ⟶ coinductionCarrier φ X :=
  equalizer.lift
    (Pi.lift (fun g => Pi.π (fun _ : G => X.V) (cosetRepresentative φ g) ≫
      (X.ρ (cosetCoordinate φ g)).asHom)) (by
    apply Pi.hom_ext
    rintro ⟨h, g⟩
    simp only [Category.assoc, coinductionRelationLeft_projection,
      coinductionRelationRight_projection, Pi.lift_comp_π, Pi.lift_comp_π_assoc]
    rw [cosetRepresentative_translate, cosetCoordinate_translate φ hφ,
      map_mul, End.mul_asHom])

/-- With products indexed by `G` and `H × G` and equalizers in `C`, an
injective `φ : H →* G`, and an `H`-action `X`, the `g`-coordinate of
`coinductionSplit φ hφ X` is exactly the input projection at the chosen
`cosetRepresentative φ g` followed by
`(X.ρ (cosetCoordinate φ g)).asHom`. This is the displayed equality of
morphisms from the product to `X.V`, not preservation of its arbitrary
original `g`-coordinate. -/
@[reassoc (attr := simp)]
theorem coinductionSplit_coordinate (hφ : Function.Injective φ) (X : Action C H) (g : G) :
    coinductionSplit φ hφ X ≫ coinductionCoordinate φ X g =
      Pi.π (fun _ : G => X.V) (cosetRepresentative φ g) ≫
        (X.ρ (cosetCoordinate φ g)).asHom := by
  change coinductionSplit φ hφ X ≫ equalizer.ι _ _ ≫ Pi.π (fun _ : G => X.V) g = _
  rw [← Category.assoc, coinductionSplit, equalizer.lift_ι, Pi.lift_comp_π]

set_option backward.isDefEq.respectTransparency false in
/-- The actual equivariance equalizer is a retract of the full product object. -/
theorem coinductionSplit_retract (hφ : Function.Injective φ) (X : Action C H) :
    equalizer.ι (coinductionRelationLeft φ X) (coinductionRelationRight X) ≫
      coinductionSplit φ hφ X = 𝟙 (coinductionCarrier φ X) := by
  apply equalizer.hom_ext
  apply Pi.hom_ext
  intro g
  have h : equalizer.ι (coinductionRelationLeft φ X) (coinductionRelationRight X) ≫
      coinductionSplit φ hφ X ≫ coinductionCoordinate φ X g =
        coinductionCoordinate φ X g := by
    rw [coinductionSplit_coordinate]
    have he := coinductionCoordinate_relation φ X (cosetCoordinate φ g) (cosetRepresentative φ g)
    rw [cosetCoordinate_factor] at he
    simpa only [coinductionCoordinate, Category.assoc] using he.symm
  simpa only [coinductionCoordinate, Category.assoc, Category.id_comp] using h

/-- The original H-action arrow gives the actual full product arrow. -/
def coinductionProductMap {X Y : Action C H} (f : X ⟶ Y) :
    coinductionProduct (G := G) X ⟶ coinductionProduct (G := G) Y :=
  Limits.Pi.map (fun _ : G => f.hom)

omit [Group G] [HasProductsOfShape (H × G) C] [HasEqualizers C] in
/-- The product arrow retains the original carrier map at every group coordinate. -/
@[reassoc (attr := simp)]
theorem coinductionProductMap_projection {X Y : Action C H} (f : X ⟶ Y) (g : G) :
    coinductionProductMap (G := G) f ≫ Pi.π (fun _ : G => Y.V) g =
      Pi.π (fun _ : G => X.V) g ≫ f.hom :=
  Limits.Pi.map_π _ _

set_option backward.isDefEq.respectTransparency false in
/-- Inclusion of the actual equalizer is natural in the original H-action map. -/
theorem coinductionMap_inclusion {X Y : Action C H} (f : X ⟶ Y) :
    coinductionMap φ f ≫ equalizer.ι (coinductionRelationLeft φ Y) (coinductionRelationRight Y) =
      equalizer.ι (coinductionRelationLeft φ X) (coinductionRelationRight X) ≫
        coinductionProductMap (G := G) f := by
  apply Pi.hom_ext
  intro g
  simpa only [coinductionCoordinate, Category.assoc, coinductionProductMap_projection]
    using coinductionMap_coordinate φ f g

set_option backward.isDefEq.respectTransparency false in
/-- The representative split is natural in the whole original H-action arrow. -/
theorem coinductionSplit_naturality (hφ : Function.Injective φ)
    {X Y : Action C H} (f : X ⟶ Y) :
    coinductionSplit φ hφ X ≫ coinductionMap φ f =
      coinductionProductMap (G := G) f ≫ coinductionSplit φ hφ Y := by
  apply equalizer.hom_ext
  apply Pi.hom_ext
  intro g
  have h : coinductionSplit φ hφ X ≫ coinductionMap φ f ≫ coinductionCoordinate φ Y g =
      coinductionProductMap (G := G) f ≫ coinductionSplit φ hφ Y ≫
        coinductionCoordinate φ Y g := by
    rw [coinductionMap_coordinate, coinductionSplit_coordinate,
      coinductionSplit_coordinate_assoc, coinductionProductMap_projection_assoc,
      f.comm]
  simpa only [coinductionCoordinate, Category.assoc] using h

/-- The actual coinduced arrow is a natural retract of the original full product arrow. -/
def coinductionArrowRetract (hφ : Function.Injective φ)
    {X Y : Action C H} (f : X ⟶ Y) :
    Retract (Arrow.mk (coinductionMap φ f)) (Arrow.mk (coinductionProductMap (G := G) f)) where
  i := Arrow.homMk (equalizer.ι _ _) (equalizer.ι _ _) (coinductionMap_inclusion φ f).symm
  r := Arrow.homMk (coinductionSplit φ hφ X) (coinductionSplit φ hφ Y)
    (coinductionSplit_naturality φ hφ f)
  retract := by
    ext
    · exact coinductionSplit_retract φ hφ X
    · exact coinductionSplit_retract φ hφ Y
section Model

variable [ModelCategory C]

omit [Group G] [HasProductsOfShape (H × G) C] [HasEqualizers C] in
/-- The full product of an underlying fibration is an underlying fibration. -/
theorem coinductionProductMap_fibration {X Y : Action C H} (f : X ⟶ Y)
    (hf : fibrations C f.hom) :
    fibrations C (coinductionProductMap (G := G) f) := by
  rw [← trivialCofibrations_rlp]
  intro A B i hi
  rw [← fibrations_llp] at hi
  let : ∀ g : G, HasLiftingProperty i (f.hom) := fun _ => hi f.hom hf
  exact inferInstanceAs (HasLiftingProperty i (Limits.Pi.map (fun _ : G => f.hom)))

omit [Group G] [HasProductsOfShape (H × G) C] [HasEqualizers C] in
/-- The full product of an underlying trivial fibration is an underlying trivial fibration. -/
theorem coinductionProductMap_trivialFibration {X Y : Action C H} (f : X ⟶ Y)
    (hf : trivialFibrations C f.hom) :
    trivialFibrations C (coinductionProductMap (G := G) f) := by
  rw [← cofibrations_rlp]
  intro A B i hi
  rw [← trivialFibrations_llp] at hi
  let : ∀ g : G, HasLiftingProperty i (f.hom) := fun _ => hi f.hom hf
  exact inferInstanceAs (HasLiftingProperty i (Limits.Pi.map (fun _ : G => f.hom)))

/-- Coinduction along an injection preserves the actual underlying fibration. -/
theorem coinductionMap_fibration (hφ : Function.Injective φ)
    {X Y : Action C H} (f : X ⟶ Y) (hf : fibrations C f.hom) :
    fibrations C (coinductionMap φ f) :=
  (fibrations C).of_retract (coinductionArrowRetract φ hφ f)
    (coinductionProductMap_fibration (G := G) f hf)

/-- Coinduction along an injection preserves the actual underlying trivial fibration. -/
theorem coinductionMap_trivialFibration (hφ : Function.Injective φ)
    {X Y : Action C H} (f : X ⟶ Y) (hf : trivialFibrations C f.hom) :
    trivialFibrations C (coinductionMap φ f) :=
  (trivialFibrations C).of_retract (coinductionArrowRetract φ hφ f)
    (coinductionProductMap_trivialFibration (G := G) f hf)

set_option backward.isDefEq.respectTransparency false in
/-- Injective subgroup restriction preserves every projective action cofibration. -/
theorem restriction_projectiveCofibration (hφ : Function.Injective φ)
    {X Y : Action C G} (i : X ⟶ Y) (hi : projectiveCofibrations C G i) :
    projectiveCofibrations C H ((Action.res C φ).map i) := by
  intro A B p hp
  have hright : ((trivialFibrations C).inverseImage (Action.forget C G))
      ((coinduction φ).map p) :=
    coinductionMap_trivialFibration φ hφ p hp
  exact (restrictionCoinductionAdjunction φ).hasLiftingProperty_iff i p |>.mpr
    (hi ((coinduction φ).map p) hright)

set_option backward.isDefEq.respectTransparency false in
/-- Injective subgroup restriction preserves every projective trivial action cofibration. -/
theorem restriction_projectiveTrivialCofibration (hφ : Function.Injective φ)
    {X Y : Action C G} (i : X ⟶ Y) (hi : projectiveTrivialCofibrations C G i) :
    projectiveTrivialCofibrations C H ((Action.res C φ).map i) := by
  intro A B p hp
  have hright : ((fibrations C).inverseImage (Action.forget C G))
      ((coinduction φ).map p) :=
    coinductionMap_fibration φ hφ p hp
  exact (restrictionCoinductionAdjunction φ).hasLiftingProperty_iff i p |>.mpr
    (hi ((coinduction φ).map p) hright)


set_option backward.isDefEq.respectTransparency false in
/-- Restriction preserves projective cofibrancy on the actual initial H-action map. -/
theorem restriction_projectiveCofibrantObject (hφ : Function.Injective φ)
    (X : Action C G) (hX : projectiveCofibrantObject C G X) :
    projectiveCofibrantObject C H ((Action.res C φ).obj X) := by
  let : (Action.res C φ).IsLeftAdjoint := (restrictionCoinductionAdjunction φ).isLeftAdjoint
  have hinit : IsInitial ((Action.res C φ).obj (⊥_ (Action C G))) :=
    IsInitial.isInitialObj (Action.res C φ) (⊥_ (Action C G)) initialIsInitial
  let e : (⊥_ (Action C H)) ≅ (Action.res C φ).obj (⊥_ (Action C G)) :=
    initialIsInitial.uniqueUpToIso hinit
  let ea : Arrow.mk (initial.to ((Action.res C φ).obj X)) ≅
      Arrow.mk ((Action.res C φ).map (initial.to X)) :=
    Arrow.isoMk e (Iso.refl _) (initialIsInitial.hom_ext _ _)
  have hmap := restriction_projectiveCofibration φ hφ (initial.to X) hX
  intro A B p hp
  exact (HasLiftingProperty.iff_of_arrow_iso_left ea p).mpr (hmap p hp)

omit [HasProductsOfShape G C] [HasEqualizers C] in
/-- The lifting definition is exactly the cofibration class of any
actual projective action model. -/
theorem projectiveCofibrations_eq [ModelCategory (Action C G)]
    (hTF : trivialFibrations (Action C G) =
      (trivialFibrations C).inverseImage (Action.forget C G)) :
    projectiveCofibrations C G = cofibrations (Action C G) := by
  unfold projectiveCofibrations
  rw [← hTF, trivialFibrations_llp]

omit [HasProductsOfShape G C] [HasEqualizers C] in
/-- The lifting definition is exactly the trivial cofibrations of that projective action model. -/
theorem projectiveTrivialCofibrations_eq [ModelCategory (Action C G)]
    (hFib : fibrations (Action C G) =
      (fibrations C).inverseImage (Action.forget C G)) :
    projectiveTrivialCofibrations C G = trivialCofibrations (Action C G) := by
  unfold projectiveTrivialCofibrations
  rw [← hFib, fibrations_llp]
end Model

end HomotopicalAlgebra.SemiModel.ProjectiveActions
