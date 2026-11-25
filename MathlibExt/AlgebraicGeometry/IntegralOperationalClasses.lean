/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IntegralGysinRecipes

/-!
# Integral operational Chow as actual compatible cap families

A degree-q class acts on every actual finite-type test scheme over X.
It commutes with proper pushforward, pure-dimension flat pullback and the
normal-cone-normalized refined Gysin operation on every Cartesian test square.
The class group is the actual subgroup of these compatible families.
Cup product is literal composition of the cap operations.

Sources: Fulton, *Intersection Theory*, chapter 17;
AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
Chow/BivariantLemmas/VirtualNormalBundleClassConstruction.lean and Chow/GysinConstruction,
Apache 2.0. The compatibility of the identity and closure under cup product
are proved here: only degree casts move.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace AlgebraicGeometry.IntegralOperationalClasses

open CategoryTheory IntegerSchemeChow IntegralOperationalChow IntegralGysinRecipes

variable {k : Type} [Field k] (O : CycleOperations (k := k)) (X : FieldScheme k)

abbrev reindex (T : TestScheme X) {Y : FieldScheme k} (f : Y.scheme ⟶ T.source.scheme) :
    TestScheme X := ⟨Y, f ≫ T.map⟩

abbrev ActionFamily (q : ℤ) :=
  ∀ (T : TestScheme X) (d : ℤ), ChowGroup T.source d →+ ChowGroup T.source (d - q)

theorem action_assoc {q : ℤ} (A : ActionFamily X q) {Z Y W : FieldScheme k}
    (f : Z.scheme ⟶ Y.scheme) (g : Y.scheme ⟶ W.scheme) (h : W.scheme ⟶ X.scheme)
    (d : ℤ) (alpha : ChowGroup Z d) :
    A ⟨Z, (f ≫ g) ≫ h⟩ d alpha = A ⟨Z, f ≫ (g ≫ h)⟩ d alpha := by
  let evaluate : (Z.scheme ⟶ X.scheme) → ChowGroup Z (d - q) :=
    fun m ↦ A ⟨Z, m⟩ d alpha
  exact congrArg evaluate (Category.assoc f g h)

structure Compatible (q : ℤ) (A : ActionFamily X q) : Prop where
  proper : ∀ (T : TestScheme X) {Y : FieldScheme k}
    (f : Y.scheme ⟶ T.source.scheme) [IsProper f.left] (d : ℤ) (alpha : ChowGroup Y d),
    O.proper f (d - q) (A (reindex X T f) d alpha) = A T d (O.proper f d alpha)
  flat : ∀ (T : TestScheme X) {Y : FieldScheme k}
    (f : Y.scheme ⟶ T.source.scheme) [Flat f.left] (r : ℕ)
    (hr : PureRelativeDimension f r) (d : ℤ) (alpha : ChowGroup T.source d),
    A (reindex X T f) (d + r) (O.flat f r hr d alpha) =
      chowCast Y (by omega) (O.flat f r hr (d - q) (A T d alpha))
  gysin : ∀ (Y : TestScheme X) {Z T : FieldScheme k}
    (i : Z.scheme ⟶ Y.source.scheme) [IsClosedImmersion i.left]
    (t : T.scheme ⟶ Y.source.scheme) (c : ℕ)
    (G : RefinedGeometry O i t c) (S : Specialization O G)
    (d : ℤ) (alpha : ChowGroup T d),
    A (reindex X Y (G.square.snd ≫ t)) (d - c) (refinedGysin O G S d alpha) =
      chowCast G.square.source (by omega)
        (refinedGysin O G S (d - q) (A (reindex X Y t) d alpha))

def group (q : ℤ) : AddSubgroup (ActionFamily X q) where
  carrier := {A | Compatible O X q A}
  zero_mem' := by
    constructor <;> intros <;> simp
  add_mem' := by
    intro A B hA hB
    constructor
    · intro T Y f h d alpha
      simp only [Pi.add_apply, AddMonoidHom.add_apply, map_add, hA.proper, hB.proper]
    · intro T Y f h r hr d alpha
      simp only [Pi.add_apply, AddMonoidHom.add_apply, map_add, hA.flat, hB.flat]
    · intro Y Z T i h t c G S d alpha
      simp only [Pi.add_apply, AddMonoidHom.add_apply, map_add, hA.gysin, hB.gysin]
  neg_mem' := by
    intro A hA
    constructor
    · intro T Y f h d alpha
      simp only [Pi.neg_apply, AddMonoidHom.neg_apply, map_neg, hA.proper]
    · intro T Y f h r hr d alpha
      simp only [Pi.neg_apply, AddMonoidHom.neg_apply, map_neg, hA.flat]
    · intro Y Z T i h t c G S d alpha
      simp only [Pi.neg_apply, AddMonoidHom.neg_apply, map_neg, hA.gysin]

abbrev Class (q : ℤ) := group O X q

def degreeCast {q r : ℤ} (h : q = r) (A : Class O X q) : Class O X r := by
  cases h
  exact A

def cupFamily {q r : ℤ} (A : Class O X q) (B : Class O X r) : ActionFamily X (q + r) :=
  fun T d ↦ (chowCast T.source (by omega)).comp ((A.val T (d - r)).comp (B.val T d))

def identityFamily : ActionFamily X 0 := fun T d ↦ chowCast T.source (by omega)

section Casts

variable {X}

theorem chowCast_chowCast (Y : FieldScheme k) {a b c : ℤ} (h : a = b) (h' : b = c)
    (x : ChowGroup Y a) : chowCast Y h' (chowCast Y h x) = chowCast Y (h.trans h') x := by
  subst h h'
  rfl

theorem chowCast_rfl (Y : FieldScheme k) {a : ℤ} (h : a = a) (x : ChowGroup Y a) :
    chowCast Y h x = x :=
  rfl

theorem action_chowCast {q : ℤ} (A : ActionFamily X q) (T : TestScheme X) {a b : ℤ}
    (h : a = b) (x : ChowGroup T.source a) :
    A T b (chowCast T.source h x) = chowCast T.source (by rw [h]) (A T a x) := by
  subst h
  rfl

theorem proper_chowCast {Y Z : FieldScheme k} (f : Y.scheme ⟶ Z.scheme) [IsProper f.left]
    {a b : ℤ} (h : a = b) (x : ChowGroup Y a) :
    O.proper f b (chowCast Y h x) = chowCast Z h (O.proper f a x) := by
  subst h
  rfl

theorem flat_chowCast {Y Z : FieldScheme k} (f : Y.scheme ⟶ Z.scheme) [Flat f.left] (r : ℕ)
    (hr : PureRelativeDimension f r) {a b : ℤ} (h : a = b) (x : ChowGroup Z a) :
    O.flat f r hr b (chowCast Z h x) = chowCast Y (by rw [h]) (O.flat f r hr a x) := by
  subst h
  rfl

theorem refinedGysin_chowCast {Z Y T : FieldScheme k} {i : Z.scheme ⟶ Y.scheme}
    [IsClosedImmersion i.left] {t : T.scheme ⟶ Y.scheme} {c : ℕ}
    (G : RefinedGeometry O i t c) (S : Specialization O G) {a b : ℤ} (h : a = b)
    (x : ChowGroup T a) :
    refinedGysin O G S b (chowCast T h x) =
      chowCast G.square.source (by rw [h]) (refinedGysin O G S a x) := by
  subst h
  rfl

end Casts

/-- The identity family commutes with every operation: only degree casts move. -/
theorem identityFamily_compatible : Compatible O X 0 (identityFamily X) where
  proper T Y f _ d alpha := proper_chowCast O f _ alpha
  flat T Y f _ r hr d alpha := by
    simp only [identityFamily]
    rw [flat_chowCast, chowCast_chowCast]
  gysin Y Z T i _ t c G S d alpha := by
    simp only [identityFamily]
    rw [refinedGysin_chowCast, chowCast_chowCast]

/-- The composite of two compatible families is compatible: apply the two
compatibility laws in turn and move the degree casts. -/
theorem cupFamily_compatible {q r : ℤ} (A : Class O X q) (B : Class O X r) :
    Compatible O X (q + r) (cupFamily O X A B) where
  proper T Y f _ d alpha := by
    simp only [cupFamily, AddMonoidHom.comp_apply]
    rw [proper_chowCast, A.property.proper, B.property.proper]
  flat T Y f _ r' hr d alpha := by
    simp only [cupFamily, AddMonoidHom.comp_apply]
    rw [B.property.flat, action_chowCast, A.property.flat, flat_chowCast]
    simp only [chowCast_chowCast]
  gysin Y Z T i _ t c G S d alpha := by
    simp only [cupFamily, AddMonoidHom.comp_apply]
    rw [B.property.gysin, action_chowCast, A.property.gysin, refinedGysin_chowCast]
    simp only [chowCast_chowCast]

/-- The cup product: literal composition of the cap operations. -/
def cupClass {q r : ℤ} (A : Class O X q) (B : Class O X r) : Class O X (q + r) :=
  ⟨cupFamily O X A B, cupFamily_compatible O X A B⟩

/-- The unit class: the identity cap operation. -/
def unitClass : Class O X 0 :=
  ⟨identityFamily X, identityFamily_compatible O X⟩

variable {X} (Y : FieldScheme k) (f : Y.scheme ⟶ X.scheme)

/-- Reindex the same cap operation along the actual scheme map. -/
def pullbackClass {q : ℤ} (A : Class O X q) : Class O Y q := by
  let B : ActionFamily Y q := fun T d ↦ A.val ⟨T.source, T.map ≫ f⟩ d
  refine ⟨B, ?_⟩
  constructor
  · intro T Z g h d alpha
    dsimp [B, reindex]
    rw [action_assoc]
    exact A.property.proper
      ⟨T.source, T.map ≫ f⟩ g d alpha
  · intro T Z g h r hr d alpha
    dsimp [B, reindex]
    rw [action_assoc]
    exact A.property.flat
      ⟨T.source, T.map ≫ f⟩ g r hr d alpha
  · intro T Z W i h t c G S d alpha
    dsimp [B, reindex]
    rw [action_assoc, action_assoc]
    exact A.property.gysin
      ⟨T.source, T.map ≫ f⟩ i t c G S d alpha

end AlgebraicGeometry.IntegralOperationalClasses
