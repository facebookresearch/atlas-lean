/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Monad.BarSimplicial
public import MathlibExt.CategoryTheory.Monad.BarFunctorial
public import MathlibExt.AlgebraicTopology.SimplicialObject.DataAugmented
public import MathlibExt.AlgebraicTopology.SimplicialObject.ToAugmented

/-!
# Bar augmentation via balanced pairings

For the bar source and face conventions, see `Bar`.

`BalancedPairing T R L` packages the augmentation data for the two-sided bar
`B(R, T, L)`: a target functor `Q : A ⥤ D` with a degree-zero map
`p : B₀ ⟶ Q` equalizing the two degree-one faces, equivalently the pointwise
action equation `R.action ≫ p = R.map L.action ≫ p`. It induces the data-level
map, the augmented data, and the genuine augmented simplicial object, with
functorial maps from a degree-zero square. The general two-sided bar has no
canonical augmentation without such balanced-pairing data.
-/

@[expose] public section

namespace CategoryTheory
namespace Monad

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type u₃} [Category.{v₃} A]

variable {T : Monad C} {R : RightModule T D} {L : LeftModule A T}

open SimplicialObject

/--
Unbundled balanced-pairing predicate for the two-sided bar.
It equalizes the two degree-one bar faces by reusing the generic
`SimplicialObject.Data.IsBalanced` predicate on `barData T R L`.
-/
def IsBalancedPairing {Q : A ⥤ D} (p : barObj T R L 0 ⟶ Q) : Prop :=
  Data.IsBalanced (X := barData T R L) p

theorem isBalancedPairing_def {Q : A ⥤ D} {p : barObj T R L 0 ⟶ Q} :
    IsBalancedPairing (T := T) (R := R) (L := L) p ↔
      Data.IsBalanced (X := barData T R L) p :=
  Iff.rfl

/--
The balancing condition `δ₀ ≫ p = δ₁ ≫ p` is exactly the pointwise
action equation `R.action ≫ p = R.map L.action ≫ p`.
-/
theorem isBalancedPairing_iff_action_eq {Q : A ⥤ D} {p : barObj T R L 0 ⟶ Q} :
    IsBalancedPairing (T := T) (R := R) (L := L) p ↔
      ∀ (a : A),
        R.action.app (L.functor.obj a) ≫ p.app a =
        R.functor.map (L.action.app a) ≫ p.app a := by
  constructor
  · intro hp a
    have h_app :
        ((barData T R L).δ (0 : Fin 2) ≫ p).app a =
        ((barData T R L).δ (1 : Fin 2) ≫ p).app a :=
      congrArg (fun (t : barObj T R L 1 ⟶ Q) => t.app a) hp
    have h0 : ((barData T R L).δ (0 : Fin 2) ≫ p).app a =
        R.action.app (L.functor.obj a) ≫ p.app a := rfl
    have h1 : ((barData T R L).δ (1 : Fin 2) ≫ p).app a =
        R.functor.map (L.action.app a) ≫ p.app a := rfl
    exact h0.symm.trans (h_app.trans h1)
  · intro h
    dsimp only [IsBalancedPairing, Data.IsBalanced]
    ext a
    have h0 : ((barData T R L).δ (0 : Fin 2) ≫ p).app a =
        R.action.app (L.functor.obj a) ≫ p.app a := rfl
    have h1 : ((barData T R L).δ (1 : Fin 2) ≫ p).app a =
        R.functor.map (L.action.app a) ≫ p.app a := rfl
    exact h0.trans ((h a).trans h1.symm)

/--
Bundled balanced pairing for the two-sided bar `B(R,T,L)`.
It consists of a target functor `Q`, a degree-zero map `p : B₀ ⟶ Q`,
and the balancing proof that `p` equalizes the two degree-one faces.
-/
structure BalancedPairing (T : Monad C) (R : RightModule T D) (L : LeftModule A T) where
  target : A ⥤ D
  pairing : barObj T R L 0 ⟶ target
  balanced : IsBalancedPairing (T := T) (R := R) (L := L) pairing

namespace BalancedPairing

variable {T : Monad C} {R : RightModule T D} {L : LeftModule A T}

variable {R' : RightModule T D} {L' : LeftModule A T}
variable {R'' : RightModule T D} {L'' : LeftModule A T}

/-- Constructor from the pointwise action equation, useful and clean. -/
def mkOfActionEq {Q : A ⥤ D} (p : barObj T R L 0 ⟶ Q)
    (h : ∀ (a : A),
      R.action.app (L.functor.obj a) ≫ p.app a =
      R.functor.map (L.action.app a) ≫ p.app a) :
    BalancedPairing T R L where
  target := Q
  pairing := p
  balanced := (isBalancedPairing_iff_action_eq (T := T) (R := R) (L := L)).mpr h

@[simp]
theorem mkOfActionEq_target {Q : A ⥤ D} (p : barObj T R L 0 ⟶ Q)
    (h : ∀ (a : A),
      R.action.app (L.functor.obj a) ≫ p.app a =
      R.functor.map (L.action.app a) ≫ p.app a) :
    (mkOfActionEq (T := T) (R := R) (L := L) p h).target = Q :=
  rfl

@[simp]
theorem mkOfActionEq_pairing {Q : A ⥤ D} (p : barObj T R L 0 ⟶ Q)
    (h : ∀ (a : A),
      R.action.app (L.functor.obj a) ≫ p.app a =
      R.functor.map (L.action.app a) ≫ p.app a) :
    (mkOfActionEq (T := T) (R := R) (L := L) p h).pairing = p :=
  rfl

/--
The data morphism `barData T R L ⟶ constData pairing.target`
obtained by reusing `Data.balancedHom`.
-/
noncomputable def toDataHom (b : BalancedPairing T R L) :
    barData T R L ⟶ Data.constData b.target :=
  Data.balancedHom b.balanced

@[simp]
theorem toDataHom_app_zero (b : BalancedPairing T R L) :
    (b.toDataHom).app 0 = b.pairing :=
  rfl

@[simp]
theorem toDataHom_app_succ (b : BalancedPairing T R L) (n : ℕ) :
    (b.toDataHom).app (n + 1) =
      (barData T R L).δ (0 : Fin (n + 2)) ≫ (b.toDataHom).app n :=
  rfl

theorem toDataHom_app (b : BalancedPairing T R L) (n : ℕ) :
    (b.toDataHom).app n = Data.balancedExtension (X := barData T R L) b.pairing n :=
  rfl

/--
Face compatibility via the generic API: every face followed by the
lower component equals the higher component.
-/
theorem toDataHom_face (b : BalancedPairing T R L) (n : ℕ) (i : Fin (n + 2)) :
    (barData T R L).δ i ≫ (b.toDataHom).app n = (b.toDataHom).app (n + 1) :=
  Data.balancedExtension_δ b.balanced n i

/-- The reversed face-compatibility equality `Hom.w_δ`. -/
theorem toDataHom_w_δ (b : BalancedPairing T R L) {n : ℕ} (i : Fin (n + 2)) :
    (b.toDataHom).app (n + 1) ≫ (Data.constData b.target).δ i =
      (barData T R L).δ i ≫ (b.toDataHom).app n := by
  have h := (b.toDataHom).w_δ i
  exact h

/-- Degeneracy compatibility via the generic API. -/
theorem toDataHom_degen (b : BalancedPairing T R L) (n : ℕ) (i : Fin (n + 1)) :
    (barData T R L).σ i ≫ (b.toDataHom).app (n + 1) = (b.toDataHom).app n :=
  Data.balancedExtension_σ b.balanced n i

theorem toDataHom_w_σ (b : BalancedPairing T R L) {n : ℕ} (i : Fin (n + 1)) :
    (b.toDataHom).app n ≫ (Data.constData b.target).σ i =
      (barData T R L).σ i ≫ (b.toDataHom).app (n + 1) := by
  have h := (b.toDataHom).w_σ i
  exact h

/-- The induced augmented simplicial data over `A ⥤ D`. -/
noncomputable def toAugmented (b : BalancedPairing T R L) :
    Data.Augmented (A ⥤ D) :=
  Data.Augmented.augment (barData T R L) b.target b.pairing b.balanced

@[simp]
theorem toAugmented_left (b : BalancedPairing T R L) :
    (b.toAugmented).left = barData T R L :=
  rfl

@[simp]
theorem toAugmented_right (b : BalancedPairing T R L) :
    (b.toAugmented).right = b.target :=
  rfl

@[simp]
theorem toAugmented_hom (b : BalancedPairing T R L) :
    (b.toAugmented).hom = b.toDataHom :=
  rfl

@[simp]
theorem toAugmented_hom_app_zero (b : BalancedPairing T R L) :
    (b.toAugmented).hom.app 0 = b.pairing :=
  rfl

@[simp]
theorem toAugmented_hom_app_succ (b : BalancedPairing T R L) (n : ℕ) :
    (b.toAugmented).hom.app (n + 1) =
      (barData T R L).δ (0 : Fin (n + 2)) ≫ (b.toAugmented).hom.app n :=
  rfl

/--
Functoriality: given module morphisms `fR : R ⟶ R'`, `fL : L ⟶ L'`,
a target morphism `q : b.target ⟶ b'.target`, and the degree-zero square
`barMap fR fL 0 ≫ b'.pairing = b.pairing ≫ q`, construct the induced map
`b.toAugmented ⟶ b'.toAugmented` in `Data.Augmented (A ⥤ D)`.
Uses the generic uniqueness theorem `Data.hom_eq_of_app_zero_eq`
to prove the comma square; no higher face/degeneracy compatibility is re-proved.
-/
noncomputable def toAugmentedMap
    (b : BalancedPairing T R L) (b' : BalancedPairing T R' L')
    (fR : R ⟶ R') (fL : L ⟶ L')
    (q : b.target ⟶ b'.target)
    (hq : barMap fR fL 0 ≫ b'.pairing = b.pairing ≫ q) :
    b.toAugmented ⟶ b'.toAugmented where
  left := barDataHom fR fL
  right := q
  w := by
    apply Data.hom_eq_of_app_zero_eq
    change barMap fR fL 0 ≫ b'.pairing = b.pairing ≫ q
    exact hq

@[simp]
theorem toAugmentedMap_left
    (b : BalancedPairing T R L) (b' : BalancedPairing T R' L')
    (fR : R ⟶ R') (fL : L ⟶ L')
    (q : b.target ⟶ b'.target)
    (hq : barMap fR fL 0 ≫ b'.pairing = b.pairing ≫ q) :
    (toAugmentedMap b b' fR fL q hq).left = barDataHom fR fL :=
  rfl

@[simp]
theorem toAugmentedMap_right
    (b : BalancedPairing T R L) (b' : BalancedPairing T R' L')
    (fR : R ⟶ R') (fL : L ⟶ L')
    (q : b.target ⟶ b'.target)
    (hq : barMap fR fL 0 ≫ b'.pairing = b.pairing ≫ q) :
    (toAugmentedMap b b' fR fL q hq).right = q :=
  rfl

@[simp]
theorem toAugmentedMap_left_app
    (b : BalancedPairing T R L) (b' : BalancedPairing T R' L')
    (fR : R ⟶ R') (fL : L ⟶ L')
    (q : b.target ⟶ b'.target)
    (hq : barMap fR fL 0 ≫ b'.pairing = b.pairing ≫ q)
    (n : ℕ) :
    (toAugmentedMap b b' fR fL q hq).left.app n = barMap fR fL n :=
  rfl

@[simp]
theorem toAugmentedMap_left_app_app
    (b : BalancedPairing T R L) (b' : BalancedPairing T R' L')
    (fR : R ⟶ R') (fL : L ⟶ L')
    (q : b.target ⟶ b'.target)
    (hq : barMap fR fL 0 ≫ b'.pairing = b.pairing ≫ q)
    (n : ℕ) (a : A) :
    ((toAugmentedMap b b' fR fL q hq).left.app n).app a =
      R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
        fR.f.app ((monadPow T n).obj (L'.functor.obj a)) :=
  rfl

/--
The comma square underlying `toAugmentedMap`, recorded as a `Data.Hom` equality,
proved via `hom_eq_of_app_zero_eq`.
-/
theorem toAugmentedMap_w_data
    (b : BalancedPairing T R L) (b' : BalancedPairing T R' L')
    (fR : R ⟶ R') (fL : L ⟶ L')
    (q : b.target ⟶ b'.target)
    (hq : barMap fR fL 0 ≫ b'.pairing = b.pairing ≫ q) :
    barDataHom fR fL ≫ b'.toDataHom =
      b.toDataHom ≫ (Data.constFunctor (C := A ⥤ D)).map q :=
  (toAugmentedMap b b' fR fL q hq).w

/-- Helper that composes two degree-zero squares into one for `barMap (fR ≫ gR) (fL ≫ gL) 0`. -/
theorem toAugmentedMap_comp_hq
    (b : BalancedPairing T R L) (b' : BalancedPairing T R' L')
    (b'' : BalancedPairing T R'' L'')
    (fR : R ⟶ R') (fL : L ⟶ L')
    (gR : R' ⟶ R'') (gL : L' ⟶ L'')
    (q : b.target ⟶ b'.target) (r : b'.target ⟶ b''.target)
    (hq1 : barMap fR fL 0 ≫ b'.pairing = b.pairing ≫ q)
    (hq2 : barMap gR gL 0 ≫ b''.pairing = b'.pairing ≫ r) :
    barMap (fR ≫ gR) (fL ≫ gL) 0 ≫ b''.pairing = b.pairing ≫ (q ≫ r) := by
  rw [← barMap_comp, Category.assoc, hq2, ← Category.assoc, hq1, Category.assoc]

/--
Augmented two-sided bar obtained by transporting `toAugmented` through the generic
`Data.Augmented ⥤ SimplicialObject.Augmented` functor.
-/
noncomputable def toSimplicialAugmented (b : BalancedPairing T R L) :
    SimplicialObject.Augmented (A ⥤ D) :=
  Data.Augmented.toSimplicialFunctor.obj b.toAugmented

@[simp]
theorem toSimplicialAugmented_left (b : BalancedPairing T R L) :
    (toSimplicialAugmented b).left = twoSidedBar T R L :=
  rfl

@[simp]
theorem toSimplicialAugmented_right (b : BalancedPairing T R L) :
    (toSimplicialAugmented b).right = b.target :=
  rfl

@[simp]
theorem toSimplicialAugmented_point_obj (b : BalancedPairing T R L) :
    (SimplicialObject.Augmented.point.obj (toSimplicialAugmented b)) = b.target :=
  rfl

@[simp]
theorem toSimplicialAugmented_drop_obj (b : BalancedPairing T R L) :
    (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented b)) =
      twoSidedBar T R L :=
  rfl

@[simp]
theorem toSimplicialAugmented_hom_app_mk (b : BalancedPairing T R L) (n : ℕ) :
    (toSimplicialAugmented b).hom.app
        (Opposite.op (SimplexCategory.mk n)) = b.toDataHom.app n := by
  have h1 : (toSimplicialAugmented b).hom =
      (Data.Augmented.toSimplicialFunctor.obj b.toAugmented).hom := rfl
  have h2 : (Data.Augmented.toSimplicialFunctor.obj b.toAugmented).hom =
      Data.toSimplicialNatTrans (b.toAugmented.hom) ≫
        (Data.constFunctorIso (C := A ⥤ D)).hom.app
          (Data.Augmented.point.obj b.toAugmented) :=
    Data.Augmented.toSimplicialFunctor_obj_hom b.toAugmented
  have h3 : (Data.Augmented.toSimplicialAugmented b.toAugmented).hom =
      Data.toSimplicialNatTrans (b.toAugmented.hom) ≫
        (Data.constFunctorIso (C := A ⥤ D)).hom.app
          (Data.Augmented.point.obj b.toAugmented) := rfl
  have h_eq : (toSimplicialAugmented b).hom =
      (Data.Augmented.toSimplicialAugmented b.toAugmented).hom :=
    h1.trans (h2.trans h3.symm)
  have step1 : (toSimplicialAugmented b).hom.app
      (Opposite.op (SimplexCategory.mk n)) =
      (Data.Augmented.toSimplicialAugmented b.toAugmented).hom.app
        (Opposite.op (SimplexCategory.mk n)) := by rw [h_eq]
  have step2 : (Data.Augmented.toSimplicialAugmented b.toAugmented).hom.app
        (Opposite.op (SimplexCategory.mk n)) =
      (b.toAugmented.hom).app n :=
    Data.Augmented.toSimplicialAugmented_hom_app_mk b.toAugmented n
  have step3 : (b.toAugmented.hom).app n = b.toDataHom.app n := rfl
  exact step1.trans (step2.trans step3)

theorem toSimplicialAugmented_hom_app (b : BalancedPairing T R L)
    (Δ : SimplexCategoryᵒᵖ) :
    (toSimplicialAugmented b).hom.app Δ =
      b.toDataHom.app (Opposite.unop Δ).len := by
  obtain ⟨⟨n⟩⟩ := Δ
  exact toSimplicialAugmented_hom_app_mk b n

/--
Augmented map obtained by applying the generic transport functor
`Data.Augmented.toSimplicialFunctor.map` to the `toAugmentedMap`.
-/
noncomputable def toSimplicialAugmentedMap
    (b : BalancedPairing T R L) (b' : BalancedPairing T R' L')
    (fR : R ⟶ R') (fL : L ⟶ L')
    (q : b.target ⟶ b'.target)
    (hq : barMap fR fL 0 ≫ b'.pairing = b.pairing ≫ q) :
    b.toSimplicialAugmented ⟶ b'.toSimplicialAugmented :=
  Data.Augmented.toSimplicialFunctor.map (toAugmentedMap b b' fR fL q hq)

@[simp]
theorem toSimplicialAugmentedMap_left
    (b : BalancedPairing T R L) (b' : BalancedPairing T R' L')
    (fR : R ⟶ R') (fL : L ⟶ L')
    (q : b.target ⟶ b'.target)
    (hq : barMap fR fL 0 ≫ b'.pairing = b.pairing ≫ q) :
    (toSimplicialAugmentedMap b b' fR fL q hq).left = twoSidedBarHom fR fL :=
  rfl

@[simp]
theorem toSimplicialAugmentedMap_right
    (b : BalancedPairing T R L) (b' : BalancedPairing T R' L')
    (fR : R ⟶ R') (fL : L ⟶ L')
    (q : b.target ⟶ b'.target)
    (hq : barMap fR fL 0 ≫ b'.pairing = b.pairing ≫ q) :
    (toSimplicialAugmentedMap b b' fR fL q hq).right = q :=
  rfl

@[simp]
theorem toSimplicialAugmentedMap_left_app_mk
    (b : BalancedPairing T R L) (b' : BalancedPairing T R' L')
    (fR : R ⟶ R') (fL : L ⟶ L')
    (q : b.target ⟶ b'.target)
    (hq : barMap fR fL 0 ≫ b'.pairing = b.pairing ≫ q)
    (n : ℕ) :
    (toSimplicialAugmentedMap b b' fR fL q hq).left.app
        (Opposite.op (SimplexCategory.mk n)) =
      barMap fR fL n :=
  rfl

theorem toSimplicialAugmentedMap_left_app
    (b : BalancedPairing T R L) (b' : BalancedPairing T R' L')
    (fR : R ⟶ R') (fL : L ⟶ L')
    (q : b.target ⟶ b'.target)
    (hq : barMap fR fL 0 ≫ b'.pairing = b.pairing ≫ q)
    (Δ : SimplexCategoryᵒᵖ) :
    (toSimplicialAugmentedMap b b' fR fL q hq).left.app Δ =
      barMap fR fL (Opposite.unop Δ).len := by
  obtain ⟨Δ⟩ := Δ
  rfl

/-- Identity law for the data-level Bar augmentation map over the canonical identity square. -/
theorem toAugmentedMap_id
    (b : BalancedPairing T R L) :
    toAugmentedMap b b (𝟙 R) (𝟙 L) (𝟙 b.target)
      (by rw [barMap_id, Category.id_comp, Category.comp_id]) =
      𝟙 b.toAugmented := by
  apply CommaMorphism.ext
  · rw [toAugmentedMap_left]
    change barDataHom (𝟙 R) (𝟙 L) = 𝟙 (barData T R L)
    exact barDataHom_id R L
  · rfl

/--
Composition law for the data-level Bar augmentation maps over genuinely
distinct `R/R'/R''`, `L/L'/L''`, and target endpoints, with the canonical
composite square from `toAugmentedMap_comp_hq`.
-/
theorem toAugmentedMap_comp
    (b : BalancedPairing T R L) (b' : BalancedPairing T R' L')
    (b'' : BalancedPairing T R'' L'')
    (fR : R ⟶ R') (fL : L ⟶ L')
    (gR : R' ⟶ R'') (gL : L' ⟶ L'')
    (q : b.target ⟶ b'.target) (r : b'.target ⟶ b''.target)
    (hq1 : barMap fR fL 0 ≫ b'.pairing = b.pairing ≫ q)
    (hq2 : barMap gR gL 0 ≫ b''.pairing = b'.pairing ≫ r) :
    toAugmentedMap b b' fR fL q hq1 ≫ toAugmentedMap b' b'' gR gL r hq2 =
      toAugmentedMap b b'' (fR ≫ gR) (fL ≫ gL) (q ≫ r)
        (toAugmentedMap_comp_hq b b' b'' fR fL gR gL q r hq1 hq2) := by
  apply CommaMorphism.ext
  · change (toAugmentedMap b b' fR fL q hq1).left ≫
        (toAugmentedMap b' b'' gR gL r hq2).left = _
    rw [toAugmentedMap_left, toAugmentedMap_left, toAugmentedMap_left]
    exact barDataHom_comp fR gR fL gL
  · rfl

/-- Identity law for the augmented Bar map over the canonical identity square. -/
theorem toSimplicialAugmentedMap_id
    (b : BalancedPairing T R L) :
    toSimplicialAugmentedMap b b (𝟙 R) (𝟙 L) (𝟙 b.target)
      (by rw [barMap_id, Category.id_comp, Category.comp_id]) =
      𝟙 (b.toSimplicialAugmented) := by
  change Data.Augmented.toSimplicialFunctor.map
      (toAugmentedMap b b (𝟙 R) (𝟙 L) (𝟙 b.target) _) = _
  rw [toAugmentedMap_id b]
  exact Functor.map_id _ _

/--
Composition law for the augmented Bar maps over genuinely distinct `R/R'/R''`, `L/L'/L''`, and
target endpoints, with the canonical composite square from `toAugmentedMap_comp_hq`.
-/
theorem toSimplicialAugmentedMap_comp
    (b : BalancedPairing T R L) (b' : BalancedPairing T R' L')
    (b'' : BalancedPairing T R'' L'')
    (fR : R ⟶ R') (fL : L ⟶ L')
    (gR : R' ⟶ R'') (gL : L' ⟶ L'')
    (q : b.target ⟶ b'.target) (r : b'.target ⟶ b''.target)
    (hq1 : barMap fR fL 0 ≫ b'.pairing = b.pairing ≫ q)
    (hq2 : barMap gR gL 0 ≫ b''.pairing = b'.pairing ≫ r) :
    toSimplicialAugmentedMap b b' fR fL q hq1 ≫
        toSimplicialAugmentedMap b' b'' gR gL r hq2 =
      toSimplicialAugmentedMap b b'' (fR ≫ gR) (fL ≫ gL) (q ≫ r)
        (toAugmentedMap_comp_hq b b' b'' fR fL gR gL q r hq1 hq2) := by
  change Data.Augmented.toSimplicialFunctor.map
        (toAugmentedMap b b' fR fL q hq1) ≫
      Data.Augmented.toSimplicialFunctor.map
        (toAugmentedMap b' b'' gR gL r hq2) =
    Data.Augmented.toSimplicialFunctor.map
      (toAugmentedMap b b'' (fR ≫ gR) (fL ≫ gL) (q ≫ r)
        (toAugmentedMap_comp_hq b b' b'' fR fL gR gL q r hq1 hq2))
  rw [← Functor.map_comp]
  congr 1
  exact toAugmentedMap_comp b b' b'' fR fL gR gL q r hq1 hq2

end BalancedPairing

end Monad
end CategoryTheory
