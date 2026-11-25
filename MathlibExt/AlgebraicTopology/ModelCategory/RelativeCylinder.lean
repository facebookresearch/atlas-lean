/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.HomotopyExtension
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Source-relative mapping-cylinder and pushout comparisons

Original source maps and endpoint/cocone equations are retained. These
constructions supply the categorical source framework used in MMSS
Definition 6.8 and its cone, cylinder and homotopy-pushout applications.
-/

set_option autoImplicit false
noncomputable section
universe u v uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.OriginalRelativeCylinder

variable {C : Type uC} [Category.{vC} C]

/-- Both relative homotopies use the given full source and retraction maps. -/
structure PairData (T : C ⥤ C) (t₀ t₁ : 𝟭 C ⟶ T) (p : T ⟶ 𝟭 C)
    {A B M : C} (i : A ⟶ B) (j : A ⟶ M) (r : M ⟶ B) where
  /-- The original target maps back to the same cylinder, preserving its source. -/
  inverse : B ⟶ M
  inverse_source : i ≫ inverse = j
  /-- The whole cylinder homotopy is fixed on the original source inclusion. -/
  cylinderHomotopy : T.obj M ⟶ M
  cylinder_zero : t₀.app M ≫ cylinderHomotopy = 𝟙 M
  cylinder_one : t₁.app M ≫ cylinderHomotopy = r ≫ inverse
  cylinder_fixed : T.map j ≫ cylinderHomotopy = p.app A ≫ j
  /-- The whole target homotopy is fixed on the original source arrow. -/
  targetHomotopy : T.obj B ⟶ B
  target_zero : t₀.app B ≫ targetHomotopy = 𝟙 B
  target_one : t₁.app B ≫ targetHomotopy = inverse ≫ r
  target_fixed : T.map i ≫ targetHomotopy = p.app A ≫ i

variable [HasPushouts C]

/-- The actual cylinder projection descends its given interval projection and identity. -/
def projection (S : C ⥤ C) (e₀ : 𝟭 C ⟶ S) (pS : S ⟶ 𝟭 C)
    (he₀p : ∀ X : C, e₀.app X ≫ pS.app X = 𝟙 X) {A B : C} (i : A ⟶ B) :
    pushout (e₀.app A) i ⟶ B :=
  pushout.desc (pS.app A ≫ i) (𝟙 B) (by
    rw [← Category.assoc, he₀p]
    simp only [Functor.id_obj, Category.id_comp, Category.comp_id])

/-- Genuine HEP constructs the inverse and BOTH source-relative homotopies.
The interval equations are structural equations, not weak-equivalence outcomes. -/
def ofHEP (T S : C ⥤ C) [PreservesColimitsOfShape WalkingSpan T]
    (t₀ t₁ : 𝟭 C ⟶ T) (pT : T ⟶ 𝟭 C)
    (e₀ e₁ : 𝟭 C ⟶ S) (pS : S ⟶ 𝟭 C)
    (he₀p : ∀ X : C, e₀.app X ≫ pS.app X = 𝟙 X)
    (a : S ⋙ T ⟶ S)
    (ha₀ : ∀ X : C, t₀.app (S.obj X) ≫ a.app X = 𝟙 (S.obj X))
    (ha₁ : ∀ X : C, t₁.app (S.obj X) ≫ a.app X = pS.app X ≫ e₁.app X)
    (haFixed : ∀ X : C, T.map (e₁.app X) ≫ a.app X = pT.app X ≫ e₁.app X)
    (haPathProjection : ∀ X : C,
      T.map (e₀.app X) ≫ a.app X ≫ pS.app X = pT.app X)
    {A B : C} (i : A ⟶ B) (hi : IntervalHomotopyExtension.property T t₀ i) :
    PairData T t₀ t₁ pT i
      (e₁.app A ≫ pushout.inl (e₀.app A) i) (projection S e₀ pS he₀p i) := by
  classical
  have ht₀ {X Y : C} (f : X ⟶ Y) : f ≫ t₀.app Y = t₀.app X ≫ T.map f := by
    have h := t₀.naturality f
    change f ≫ t₀.app Y = t₀.app X ≫ T.map f at h
    exact h
  have ht₁ {X Y : C} (f : X ⟶ Y) : f ≫ t₁.app Y = t₁.app X ≫ T.map f := by
    have h := t₁.naturality f
    change f ≫ t₁.app Y = t₁.app X ≫ T.map f at h
    exact h
  let M := pushout (e₀.app A) i
  let l : S.obj A ⟶ M := pushout.inl (e₀.app A) i
  let b : B ⟶ M := pushout.inr (e₀.app A) i
  let j : A ⟶ M := e₁.app A ≫ l
  let r : M ⟶ B := projection S e₀ pS he₀p i
  let K : T.obj A ⟶ M := T.map (e₀.app A) ≫ a.app A ≫ l
  have hK₀ : t₀.app A ≫ K = i ≫ b := by
    change t₀.app A ≫ T.map (e₀.app A) ≫ a.app A ≫ l = i ≫ b
    rw [← Category.assoc, ← ht₀ (X := A) (Y := S.obj A) (e₀.app A), Category.assoc,
      ← Category.assoc (t₀.app (S.obj A)), ha₀ A]
    simpa only [Functor.id_obj, Category.id_comp] using
      (pushout.condition (f := e₀.app A) (g := i))
  have hK₁ : t₁.app A ≫ K = j := by
    change t₁.app A ≫ T.map (e₀.app A) ≫ a.app A ≫ l = e₁.app A ≫ l
    rw [← Category.assoc, ← ht₁ (X := A) (Y := S.obj A) (e₀.app A), Category.assoc,
      ← Category.assoc (t₁.app (S.obj A)), ha₁ A, Category.assoc,
      ← Category.assoc (e₀.app A), he₀p A]
    simp only [Functor.id_obj, Category.id_comp]
  let hExtension := hi M b K hK₀
  let L : T.obj B ⟶ M := Classical.choose hExtension
  have hL₀ : t₀.app B ≫ L = b := (Classical.choose_spec hExtension).1
  have hLi : T.map i ≫ L = K := (Classical.choose_spec hExtension).2
  let s : B ⟶ M := t₁.app B ≫ L
  have his : i ≫ s = j := by
    change i ≫ t₁.app B ≫ L = j
    rw [← Category.assoc, ht₁ i, Category.assoc, hLi]
    exact hK₁
  have hlr : l ≫ r = pS.app A ≫ i := pushout.inl_desc _ _ _
  have hbr : b ≫ r = 𝟙 B := pushout.inr_desc _ _ _
  let sqT := (IsPushout.of_hasPushout (e₀.app A) i).map T
  let H : T.obj M ⟶ M := sqT.desc (a.app A ≫ l) L hLi.symm
  have hHl : T.map l ≫ H = a.app A ≫ l := sqT.inl_desc _ _ _
  have hHb : T.map b ≫ H = L := sqT.inr_desc _ _ _
  have hH₀ : t₀.app M ≫ H = 𝟙 M := by
    apply pushout.hom_ext
    · change l ≫ (t₀.app M ≫ H) = l ≫ 𝟙 M
      rw [← Category.assoc, ht₀ l, Category.assoc, hHl,
        ← Category.assoc, ha₀, Category.id_comp, Category.comp_id]
    · change b ≫ (t₀.app M ≫ H) = b ≫ 𝟙 M
      rw [← Category.assoc, ht₀ b, Category.assoc, hHb, hL₀,
        Category.comp_id]
  have hH₁ : t₁.app M ≫ H = r ≫ s := by
    apply pushout.hom_ext
    · change l ≫ (t₁.app M ≫ H) = l ≫ (r ≫ s)
      rw [← Category.assoc, ht₁ l, Category.assoc, hHl,
        ← Category.assoc, ha₁, Category.assoc, ← Category.assoc l, hlr,
        Category.assoc, his]
    · change b ≫ (t₁.app M ≫ H) = b ≫ (r ≫ s)
      rw [← Category.assoc, ht₁ b, Category.assoc, hHb,
        ← Category.assoc b, hbr, Category.id_comp]
  have hHfixed : T.map j ≫ H = pT.app A ≫ j := by
    change T.map (e₁.app A ≫ l) ≫ H = pT.app A ≫ (e₁.app A ≫ l)
    rw [T.map_comp, Category.assoc, hHl, ← Category.assoc, haFixed,
      Category.assoc]
  have hKprojection : K ≫ r = pT.app A ≫ i := by
    change (T.map (e₀.app A) ≫ a.app A ≫ l) ≫ r = pT.app A ≫ i
    rw [Category.assoc, Category.assoc, hlr]
    simpa only [Category.assoc] using
      congrArg (fun f : T.obj A ⟶ A => f ≫ i) (haPathProjection A)
  let J : T.obj B ⟶ B := L ≫ r
  have hJ₀ : t₀.app B ≫ J = 𝟙 B := by
    change t₀.app B ≫ (L ≫ r) = 𝟙 B
    rw [← Category.assoc, hL₀, hbr]
  have hJ₁ : t₁.app B ≫ J = s ≫ r := (Category.assoc _ _ _).symm
  have hJfixed : T.map i ≫ J = pT.app A ≫ i := by
    change T.map i ≫ (L ≫ r) = pT.app A ≫ i
    rw [← Category.assoc, hLi, hKprojection]
  exact {
    inverse := s
    inverse_source := his
    cylinderHomotopy := H
    cylinder_zero := hH₀
    cylinder_one := hH₁
    cylinder_fixed := hHfixed
    targetHomotopy := J
    target_zero := hJ₀
    target_one := hJ₁
    target_fixed := hJfixed }

/-- The comparison uses the caller's original two pushouts and original projection map. -/
def pushoutComparison
    {A B M Z P Q : C} {i : A ⟶ B} {j : A ⟶ M} {r : M ⟶ B} {z : A ⟶ Z}
    {kB : B ⟶ P} {kZ : Z ⟶ P} (sqP : IsPushout i z kB kZ)
    {dM : M ⟶ Q} {dZ : Z ⟶ Q} (sqQ : IsPushout j z dM dZ)
    (hjr : j ≫ r = i) : Q ⟶ P :=
  sqQ.desc (r ≫ kB) kZ (by rw [← Category.assoc, hjr, sqP.w])

omit [HasPushouts C] in
/-- The complete original cylinder leg is retained by the actual pushout comparison. -/
@[reassoc]
theorem pushoutComparison_inl
    {A B M Z P Q : C} {i : A ⟶ B} {j : A ⟶ M} {r : M ⟶ B} {z : A ⟶ Z}
    {kB : B ⟶ P} {kZ : Z ⟶ P} (sqP : IsPushout i z kB kZ)
    {dM : M ⟶ Q} {dZ : Z ⟶ Q} (sqQ : IsPushout j z dM dZ)
    (hjr : j ≫ r = i) : dM ≫ pushoutComparison sqP sqQ hjr = r ≫ kB :=
  sqQ.inl_desc _ _ _

omit [HasPushouts C] in
/-- The entire original second leg is retained by the actual comparison. -/
@[reassoc]
theorem pushoutComparison_inr
    {A B M Z P Q : C} {i : A ⟶ B} {j : A ⟶ M} {r : M ⟶ B} {z : A ⟶ Z}
    {kB : B ⟶ P} {kZ : Z ⟶ P} (sqP : IsPushout i z kB kZ)
    {dM : M ⟶ Q} {dZ : Z ⟶ Q} (sqQ : IsPushout j z dM dZ)
    (hjr : j ≫ r = i) : dZ ≫ pushoutComparison sqP sqQ hjr = kZ :=
  sqQ.inr_desc _ _ _

/-- Both relative homotopies descend through the caller's actual original pushouts. -/
def cobasePair (T : C ⥤ C) [PreservesColimitsOfShape WalkingSpan T]
    (t₀ t₁ : 𝟭 C ⟶ T) (pT : T ⟶ 𝟭 C)
    (hp₀ : ∀ X : C, t₀.app X ≫ pT.app X = 𝟙 X)
    (hp₁ : ∀ X : C, t₁.app X ≫ pT.app X = 𝟙 X)
    {A B M Z P Q : C} {i : A ⟶ B} {j : A ⟶ M} {r : M ⟶ B}
    (d : PairData T t₀ t₁ pT i j r) (hjr : j ≫ r = i) (z : A ⟶ Z)
    {kB : B ⟶ P} {kZ : Z ⟶ P} (sqP : IsPushout i z kB kZ)
    {dM : M ⟶ Q} {dZ : Z ⟶ Q} (sqQ : IsPushout j z dM dZ) :
    PairData T t₀ t₁ pT kZ dZ (pushoutComparison sqP sqQ hjr) := by
  have ht₀ {X Y : C} (f : X ⟶ Y) : f ≫ t₀.app Y = t₀.app X ≫ T.map f := by
    exact t₀.naturality f
  have ht₁ {X Y : C} (f : X ⟶ Y) : f ≫ t₁.app Y = t₁.app X ≫ T.map f := by
    exact t₁.naturality f
  have hn : T.map z ≫ pT.app Z = pT.app A ≫ z := by
    exact pT.naturality z
  let c : Q ⟶ P := pushoutComparison sqP sqQ hjr
  let v : P ⟶ Q := sqP.desc (d.inverse ≫ dM) dZ (by
    rw [← Category.assoc, d.inverse_source, sqQ.w])
  have hcvM : dM ≫ c = r ≫ kB := pushoutComparison_inl sqP sqQ hjr
  have hcvZ : dZ ≫ c = kZ := pushoutComparison_inr sqP sqQ hjr
  have hvB : kB ≫ v = d.inverse ≫ dM := sqP.inl_desc _ _ _
  have hvZ : kZ ≫ v = dZ := sqP.inr_desc _ _ _
  have hHCompatible : T.map j ≫ (d.cylinderHomotopy ≫ dM) =
      T.map z ≫ (pT.app Z ≫ dZ) := by
    rw [← Category.assoc, d.cylinder_fixed, Category.assoc,
      sqQ.w, ← Category.assoc, ← hn, Category.assoc]
  let H : T.obj Q ⟶ Q := (sqQ.map T).desc
    (d.cylinderHomotopy ≫ dM) (pT.app Z ≫ dZ) hHCompatible
  have hHM : T.map dM ≫ H = d.cylinderHomotopy ≫ dM := (sqQ.map T).inl_desc _ _ _
  have hHZ : T.map dZ ≫ H = pT.app Z ≫ dZ := (sqQ.map T).inr_desc _ _ _
  have hJCompatible : T.map i ≫ (d.targetHomotopy ≫ kB) =
      T.map z ≫ (pT.app Z ≫ kZ) := by
    rw [← Category.assoc, d.target_fixed, Category.assoc,
      sqP.w, ← Category.assoc, ← hn, Category.assoc]
  let J : T.obj P ⟶ P := (sqP.map T).desc
    (d.targetHomotopy ≫ kB) (pT.app Z ≫ kZ) hJCompatible
  have hJB : T.map kB ≫ J = d.targetHomotopy ≫ kB := (sqP.map T).inl_desc _ _ _
  have hJZ : T.map kZ ≫ J = pT.app Z ≫ kZ := (sqP.map T).inr_desc _ _ _
  have hH₀ : t₀.app Q ≫ H = 𝟙 Q := by
    apply sqQ.hom_ext
    · rw [← Category.assoc, ht₀ dM, Category.assoc, hHM,
        ← Category.assoc, d.cylinder_zero, Category.id_comp, Category.comp_id]
    · rw [← Category.assoc, ht₀ dZ, Category.assoc, hHZ,
        ← Category.assoc, hp₀ Z]
      simp only [Functor.id_obj, Category.id_comp, Category.comp_id]
  have hH₁ : t₁.app Q ≫ H = c ≫ v := by
    apply sqQ.hom_ext
    · rw [← Category.assoc, ht₁ dM, Category.assoc, hHM,
        ← Category.assoc, d.cylinder_one, Category.assoc,
        ← Category.assoc dM, hcvM, Category.assoc, hvB]
    · rw [← Category.assoc, ht₁ dZ, Category.assoc, hHZ,
        ← Category.assoc, hp₁ Z, Category.id_comp,
        ← Category.assoc dZ, hcvZ, hvZ]
  have hJ₀ : t₀.app P ≫ J = 𝟙 P := by
    apply sqP.hom_ext
    · rw [← Category.assoc, ht₀ kB, Category.assoc, hJB,
        ← Category.assoc, d.target_zero, Category.id_comp, Category.comp_id]
    · rw [← Category.assoc, ht₀ kZ, Category.assoc, hJZ,
        ← Category.assoc, hp₀ Z]
      simp only [Functor.id_obj, Category.id_comp, Category.comp_id]
  have hJ₁ : t₁.app P ≫ J = v ≫ c := by
    apply sqP.hom_ext
    · rw [← Category.assoc, ht₁ kB, Category.assoc, hJB,
        ← Category.assoc, d.target_one, Category.assoc,
        ← Category.assoc kB, hvB, Category.assoc, hcvM]
    · rw [← Category.assoc, ht₁ kZ, Category.assoc, hJZ,
        ← Category.assoc, hp₁ Z, Category.id_comp,
        ← Category.assoc kZ, hvZ, hcvZ]
  exact {
    inverse := v
    inverse_source := hvZ
    cylinderHomotopy := H
    cylinder_zero := hH₀
    cylinder_one := hH₁
    cylinder_fixed := hHZ
    targetHomotopy := J
    target_zero := hJ₀
    target_one := hJ₁
    target_fixed := hJZ }

omit [HasPushouts C] in
/-- Conjugating an actual action retains its whole original input functor. -/
def conjugateAction (T S : C ⥤ C) (a : S ⋙ T ⟶ S) (e : S ≅ S) : S ⋙ T ⟶ S where
  app X := T.map (e.hom.app X) ≫ a.app X ≫ e.inv.app X
  naturality X Y f := by
    change T.map (S.map f) ≫ (T.map (e.hom.app Y) ≫ a.app Y ≫ e.inv.app Y) =
      (T.map (e.hom.app X) ≫ a.app X ≫ e.inv.app X) ≫ S.map f
    have ha : T.map (S.map f) ≫ a.app Y = a.app X ≫ S.map f := by
      exact a.naturality f
    rw [← Category.assoc, ← T.map_comp, e.hom.naturality f, T.map_comp,
      Category.assoc, ← Category.assoc (T.map (S.map f)), ha,
      Category.assoc, e.inv.naturality f]
    simp only [Category.assoc]

omit [HasPushouts C] in
/-- The original zero endpoint remains the identity after conjugating the complete action. -/
theorem conjugateAction_zero (T S : C ⥤ C) (t : 𝟭 C ⟶ T)
    (a : S ⋙ T ⟶ S) (e : S ≅ S)
    (ha : ∀ X : C, t.app (S.obj X) ≫ a.app X = 𝟙 (S.obj X)) (X : C) :
    t.app (S.obj X) ≫ (conjugateAction T S a e).app X = 𝟙 (S.obj X) := by
  have hn : t.app (S.obj X) ≫ T.map (e.hom.app X) =
      e.hom.app X ≫ t.app (S.obj X) := by
    exact (t.naturality (e.hom.app X)).symm
  change t.app (S.obj X) ≫ (T.map (e.hom.app X) ≫ a.app X ≫ e.inv.app X) = _
  rw [← Category.assoc, hn, Category.assoc, ← Category.assoc (t.app (S.obj X)),
    ha X]
  simpa only [Functor.id_obj, Category.id_comp] using Iso.hom_inv_id_app e X

omit [HasPushouts C] in
/-- The final contraction endpoint keeps the full projection and reflected endpoint. -/
theorem conjugateAction_one (T S : C ⥤ C) (t : 𝟭 C ⟶ T)
    (a : S ⋙ T ⟶ S) (e : S ≅ S) (e₀ e₁ : 𝟭 C ⟶ S) (pS : S ⟶ 𝟭 C)
    (ha : ∀ X : C, t.app (S.obj X) ≫ a.app X = pS.app X ≫ e₀.app X)
    (hp : ∀ X : C, e.hom.app X ≫ pS.app X = pS.app X)
    (he : ∀ X : C, e₀.app X ≫ e.inv.app X = e₁.app X) (X : C) :
    t.app (S.obj X) ≫ (conjugateAction T S a e).app X = pS.app X ≫ e₁.app X := by
  have hn : t.app (S.obj X) ≫ T.map (e.hom.app X) =
      e.hom.app X ≫ t.app (S.obj X) := by
    exact (t.naturality (e.hom.app X)).symm
  change t.app (S.obj X) ≫ (T.map (e.hom.app X) ≫ a.app X ≫ e.inv.app X) = _
  rw [← Category.assoc, hn, Category.assoc, ← Category.assoc (t.app (S.obj X)),
    ha X, Category.assoc, ← Category.assoc (e.hom.app X), hp X, he X]

omit [HasPushouts C] in
/-- The reflected original free endpoint is fixed throughout the whole original time action. -/
theorem conjugateAction_fixed (T S : C ⥤ C) (a : S ⋙ T ⟶ S) (e : S ≅ S)
    (e₀ e₁ : 𝟭 C ⟶ S) (pT : T ⟶ 𝟭 C)
    (ha : ∀ X : C, T.map (e₀.app X) ≫ a.app X = pT.app X ≫ e₀.app X)
    (hf : ∀ X : C, e₁.app X ≫ e.hom.app X = e₀.app X)
    (hi : ∀ X : C, e₀.app X ≫ e.inv.app X = e₁.app X) (X : C) :
    T.map (e₁.app X) ≫ (conjugateAction T S a e).app X = pT.app X ≫ e₁.app X := by
  change T.map (e₁.app X) ≫ (T.map (e.hom.app X) ≫ a.app X ≫ e.inv.app X) = _
  rw [← Category.assoc, ← T.map_comp, hf X, ← Category.assoc, ha X,
    Category.assoc, hi X]

omit [HasPushouts C] in
/-- Inverting the genuine reflection keeps the complete original endpoint equation. -/
theorem inverse_endpoint {A X : C} (e : X ≅ X) (e₀ e₁ : A ⟶ X)
    (h : e₁ ≫ e.hom = e₀) : e₀ ≫ e.inv = e₁ := by
  apply (cancel_mono e.hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact h.symm

omit [HasPushouts C] in
/-- An invariant original projection is invariant under the full inverse isomorphism. -/
theorem inverse_projection {X A : C} (e : X ≅ X) (p : X ⟶ A)
    (h : e.hom ≫ p = p) : e.inv ≫ p = p := by
  apply (cancel_epi e.hom).1
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact h.symm

omit [HasPushouts C] in
/-- The whole original action projection is retained after conjugation. -/
theorem conjugateAction_projection (T S : C ⥤ C) (a : S ⋙ T ⟶ S) (e : S ≅ S)
    (pT : T ⟶ 𝟭 C) (pS : S ⟶ 𝟭 C)
    (ha : ∀ X : C, a.app X ≫ pS.app X = pT.app (S.obj X) ≫ pS.app X)
    (hp : ∀ X : C, e.hom.app X ≫ pS.app X = pS.app X)
    (hi : ∀ X : C, e.inv.app X ≫ pS.app X = pS.app X) (X : C) :
    (conjugateAction T S a e).app X ≫ pS.app X = pT.app (S.obj X) ≫ pS.app X := by
  have hn : T.map (e.hom.app X) ≫ pT.app (S.obj X) =
      pT.app (S.obj X) ≫ e.hom.app X := by
    exact pT.naturality (e.hom.app X)
  change (T.map (e.hom.app X) ≫ a.app X ≫ e.inv.app X) ≫ pS.app X = _
  rw [Category.assoc, Category.assoc, hi X, ha X, ← Category.assoc, hn,
    Category.assoc, hp X]

end CategoryTheory.OriginalRelativeCylinder
