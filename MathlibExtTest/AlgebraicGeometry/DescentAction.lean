/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.DescentAction

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

-- `exactSource` consumer with the original binders.
example {S S' : Scheme.{u}} (s : S' ⟶ S) {X' : Scheme.{u}} {x' : X' ⟶ S'}
    (A : DescentAction s x')
    {Y : Scheme.{u}} (p : X' ⟶ Y) [Flat p] [Surjective p] [QuasiCompact p]
    (w : pullback.fst (x' ≫ s) s ≫ p = A.act ≫ p)
    (hR : IsPullback (pullback.fst (x' ≫ s) s) A.act p p)
    (f : Y ⟶ S) (hpf : p ≫ f = x' ≫ s) :
    ∃ (e : pullback f s ≅ X') (he : e.hom ≫ x' = pullback.snd f s),
      e.inv = pullback.lift p x' hpf ∧
      pullback.map (pullback.snd f s ≫ s) s (x' ≫ s) s e.hom (𝟙 S') (𝟙 S)
          (by rw [Category.comp_id, ← Category.assoc, he])
          (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
        (DescentAction.canonical s f).act ≫ e.hom :=
  DescentAction.effective_of_isPullback_of_flat_surjective s A p w hR f hpf

-- `exactSource` consumer with the original binders.
example (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']
    [Module.Finite R R'] [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    {X' : Scheme.{u}} {x' : X' ⟶ Spec (CommRingCat.of R')}
    (A : DescentAction (Spec.map (CommRingCat.ofHom (algebraMap R R'))) x')
    (haff : ∀ S : Finset X', ∃ U : X'.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U) :
    A.Effective :=
  DescentAction.effective_of_finiteEtale R R' A haff

-- Higher-universe consumer.
example (R : Type (u + 1)) [CommRing R] (R' : Type (u + 1)) [CommRing R'] [Algebra R R']
    [Module.Finite R R'] [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    {X' : Scheme.{u + 1}} {x' : X' ⟶ Spec (CommRingCat.of R')}
    (A : DescentAction (Spec.map (CommRingCat.ofHom (algebraMap R R'))) x')
    (haff : ∀ S : Finset X', ∃ U : X'.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U) :
    A.Effective :=
  DescentAction.effective_of_finiteEtale R R' A haff

-- Boundary: a canonical action is effective, witnessed by the identity.
example {S S' X : Scheme.{u}} (s : S' ⟶ S) (f : X ⟶ S) :
    (DescentAction.canonical s f).Effective := by
  refine ⟨X, f, Iso.refl _, by simp, ?_⟩
  apply pullback.hom_ext <;> simp [DescentAction.canonical]

-- The canonical action keeps the point of `X` and moves the point of `S'`: it sends
-- `((x, b), c)` to `(x, c)`.
example {S S' X T : Scheme.{u}} (s : S' ⟶ S) (f : X ⟶ S) (x : T ⟶ X) (b c : T ⟶ S')
    (hb : x ≫ f = b ≫ s) (hc : b ≫ s = c ≫ s) :
    pullback.lift (pullback.lift x b hb) c (by simpa using hc) ≫
        (DescentAction.canonical s f).act =
      pullback.lift x c (hb.trans hc) := by
  apply pullback.hom_ext <;> simp [DescentAction.canonical]

-- The unit and cocycle conditions make every action invertible: `act (act (a, b), x' a) = a`.
example {S S' X' : Scheme.{u}} (s : S' ⟶ S) {x' : X' ⟶ S'} (A : DescentAction s x') :
    pullback.lift A.act (pullback.fst (x' ≫ s) s ≫ x')
        (by rw [reassoc_of% A.act_comp, Category.assoc]; exact pullback.condition.symm) ≫
      A.act = pullback.fst (x' ≫ s) s := by
  have h : DescentAction.toTriple s x' ≫ DescentAction.actMap A.act A.act_comp =
      pullback.lift A.act (pullback.fst (x' ≫ s) s ≫ x')
        (by rw [reassoc_of% A.act_comp, Category.assoc]; exact pullback.condition.symm) := by
    apply pullback.hom_ext <;> simp
  rw [← h, Category.assoc, A.trans, ← Category.assoc, DescentAction.toTriple_proj₁₃,
    Category.assoc, A.unit_act, Category.comp_id]

-- Finite locally free descent needs neither étaleness nor faithful flatness.
example (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']
    [Module.Finite R R'] [Module.Flat R R'] [Algebra.FinitePresentation R R']
    {X' : Scheme.{u}} {x' : X' ⟶ Spec (CommRingCat.of R')}
    (A : DescentAction (Spec.map (CommRingCat.ofHom (algebraMap R R'))) x')
    (haff : ∀ F : Finset X', ∃ U : X'.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) :
    A.Effective := by
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.mpr inferInstance)
  have : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  exact DescentAction.effective_of_finiteLocallyFree _ A haff
