/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_DescentAction.lean`,
`Theorems/Thm_AlgebraicGeometry_DescentAction_effective_of_isPullback_of_flat_surjective.lean`,
`P2M/Sol/S_AlgebraicGeometry_DescentAction_effective_of_isPullback_of_flat_surjective.lean`,
`Theorems/Thm_AlgebraicGeometry_DescentAction_effective_of_finiteEtale.lean`, and
`P2M/Sol/S_AlgebraicGeometry_DescentAction_effective_of_finiteEtale.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.Etale.Finite
import MathlibExt.AlgebraicGeometry.FiniteLocallyFreeQuotient

/-!
# Descent actions along a morphism of schemes

For `s : S' ⟶ S` and a scheme `x' : X' ⟶ S'` over `S'`, a descent action is a morphism
`act : X' ×_S S' ⟶ X'` over the second projection satisfying unit and cocycle conditions.
The base change `X ×_S S'` of any `X ⟶ S` carries a canonical descent action, and a
descent action is effective when it is isomorphic to a canonical one.

## Main results

* `AlgebraicGeometry.DescentAction.effective_of_isPullback_of_flat_surjective`: an action
  whose graph is the kernel pair of a flat, surjective, quasi-compact map `p : X' ⟶ Y` over
  `S` descends to `Y`.
* `AlgebraicGeometry.DescentAction.effective_of_finiteLocallyFree`: along a finite, flat,
  finitely presented morphism, a descent action on a scheme in which every finite set of
  points lies in an affine open is effective.
* `AlgebraicGeometry.DescentAction.effective_of_finiteEtale`: the case of a finite étale
  faithfully flat ring map.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace DescentAction

variable {S S' : Scheme.{u}} (s : S' ⟶ S) {X' : Scheme.{u}} (x' : X' ⟶ S')

/-- The diagonal-type section `X' ⟶ X' ×_S S'` given by `(𝟙, x')`. -/
noncomputable def unitMap : X' ⟶ pullback (x' ≫ s) s :=
  pullback.lift (𝟙 X') x' (by rw [Category.id_comp])

/-- The projection `(X' ×_S S') ×_S S' ⟶ X' ×_S S'` forgetting the middle factor. -/
noncomputable def proj₁₃ :
    pullback (pullback.snd (x' ≫ s) s ≫ s) s ⟶ pullback (x' ≫ s) s :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _)
    (by rw [Category.assoc, pullback.condition]; exact pullback.condition)

/-- The first projection of `unitMap` is the identity. -/
@[reassoc (attr := simp)]
theorem unitMap_fst : unitMap s x' ≫ pullback.fst _ _ = 𝟙 X' :=
  pullback.lift_fst _ _ _

/-- The second projection of `unitMap` is `x'`. -/
@[reassoc (attr := simp)]
theorem unitMap_snd : unitMap s x' ≫ pullback.snd _ _ = x' :=
  pullback.lift_snd _ _ _

/-- The first projection of `proj₁₃` is the first coordinate of the triple. -/
@[reassoc (attr := simp)]
theorem proj₁₃_fst :
    proj₁₃ s x' ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- The second projection of `proj₁₃` is the last coordinate of the triple. -/
@[reassoc (attr := simp)]
theorem proj₁₃_snd : proj₁₃ s x' ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- The map `X' ×_S S' ⟶ (X' ×_S S') ×_S S'` sending `(a, b)` to `((a, b), x' a)`. -/
noncomputable def toTriple :
    pullback (x' ≫ s) s ⟶ pullback (pullback.snd (x' ≫ s) s ≫ s) s :=
  pullback.lift (𝟙 _) (pullback.fst _ _ ≫ x')
    (by rw [Category.id_comp, Category.assoc]; exact pullback.condition.symm)

/-- The first projection of `toTriple` is the identity. -/
@[reassoc (attr := simp)]
theorem toTriple_fst : toTriple s x' ≫ pullback.fst _ _ = 𝟙 _ :=
  pullback.lift_fst _ _ _

/-- The second projection of `toTriple` is `fst ≫ x'`. -/
@[reassoc (attr := simp)]
theorem toTriple_snd : toTriple s x' ≫ pullback.snd _ _ = pullback.fst _ _ ≫ x' :=
  pullback.lift_snd _ _ _

/-- Composing `toTriple` with `proj₁₃` factors through `unitMap`. -/
theorem toTriple_proj₁₃ : toTriple s x' ≫ proj₁₃ s x' = pullback.fst _ _ ≫ unitMap s x' := by
  apply pullback.hom_ext
  · rw [Category.assoc, proj₁₃_fst, toTriple_fst_assoc, Category.assoc, unitMap_fst,
      Category.comp_id]
  · rw [Category.assoc, proj₁₃_snd, toTriple_snd, Category.assoc, unitMap_snd]

variable {s x'}

/-- The map `(X' ×_S S') ×_S S' ⟶ X' ×_S S'` applying `act` to the first two factors. -/
noncomputable def actMap (act : pullback (x' ≫ s) s ⟶ X') (h : act ≫ x' = pullback.snd _ _) :
    pullback (pullback.snd (x' ≫ s) s ≫ s) s ⟶ pullback (x' ≫ s) s :=
  pullback.lift (pullback.fst _ _ ≫ act) (pullback.snd _ _)
    (by rw [Category.assoc, reassoc_of% h]; exact pullback.condition)

/-- The first projection of `actMap` applies `act`. -/
@[reassoc (attr := simp)]
theorem actMap_fst (act : pullback (x' ≫ s) s ⟶ X') (h : act ≫ x' = pullback.snd _ _) :
    actMap act h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ act :=
  pullback.lift_fst _ _ _

/-- The second projection of `actMap` is the last coordinate. -/
@[reassoc (attr := simp)]
theorem actMap_snd (act : pullback (x' ≫ s) s ⟶ X') (h : act ≫ x' = pullback.snd _ _) :
    actMap act h ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

variable (s)

/-- The canonical action map `(X ×_S S') ×_S S' ⟶ X ×_S S'` of a base change. -/
noncomputable def flipMap {X : Scheme.{u}} (f : X ⟶ S) :
    pullback (pullback.snd f s ≫ s) s ⟶ pullback f s :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst f s) (pullback.snd _ _)
    (by rw [Category.assoc, pullback.condition]; exact pullback.condition)

/-- The first projection of `flipMap` is the projection to `X`. -/
@[reassoc (attr := simp)]
theorem flipMap_fst {X : Scheme.{u}} (f : X ⟶ S) :
    flipMap s f ≫ pullback.fst f s = pullback.fst _ _ ≫ pullback.fst f s :=
  pullback.lift_fst _ _ _

/-- The second projection of `flipMap` is the last coordinate. -/
@[reassoc (attr := simp)]
theorem flipMap_snd {X : Scheme.{u}} (f : X ⟶ S) :
    flipMap s f ≫ pullback.snd f s = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

end DescentAction

/-- A descent action along `s : S' ⟶ S` on `x' : X' ⟶ S'`: a map `act : X' ×_S S' ⟶ X'`
over the second projection satisfying the unit and cocycle conditions. -/
structure DescentAction {S S' : Scheme.{u}} (s : S' ⟶ S) {X' : Scheme.{u}} (x' : X' ⟶ S') where
  /-- The action map. -/
  act : pullback (x' ≫ s) s ⟶ X'
  /-- The action map lies over the second projection. -/
  act_comp : act ≫ x' = pullback.snd _ _
  /-- The unit section acts trivially. -/
  unit_act : DescentAction.unitMap s x' ≫ act = 𝟙 X'
  /-- The cocycle condition. -/
  trans : DescentAction.actMap act act_comp ≫ act = DescentAction.proj₁₃ s x' ≫ act

namespace DescentAction

variable {S S' : Scheme.{u}} (s : S' ⟶ S)

/-- The canonical descent action on the base change `X ×_S S'` of `f : X ⟶ S`. -/
noncomputable def canonical {X : Scheme.{u}} (f : X ⟶ S) : DescentAction s (pullback.snd f s) where
  act := flipMap s f
  act_comp := flipMap_snd s f
  unit_act := by
    apply pullback.hom_ext
    · rw [Category.assoc, flipMap_fst, unitMap_fst_assoc, Category.id_comp]
    · rw [Category.assoc, flipMap_snd, unitMap_snd, Category.id_comp]
  trans := by
    apply pullback.hom_ext
    · rw [Category.assoc, flipMap_fst, actMap_fst_assoc, flipMap_fst, Category.assoc, flipMap_fst,
        proj₁₃_fst_assoc]
    · rw [Category.assoc, flipMap_snd, actMap_snd, Category.assoc, flipMap_snd, proj₁₃_snd]

variable {s}

/-- A descent action is effective if it is isomorphic over `S'` to the canonical action on
the base change of some `f : X ⟶ S`. -/
def Effective {X' : Scheme.{u}} {x' : X' ⟶ S'} (A : DescentAction s x') : Prop :=
  ∃ (X : Scheme.{u}) (f : X ⟶ S) (e : pullback f s ≅ X') (he : e.hom ≫ x' = pullback.snd f s),
    pullback.map (pullback.snd f s ≫ s) s (x' ≫ s) s e.hom (𝟙 S') (𝟙 S)
        (by rw [Category.comp_id, ← Category.assoc, he])
        (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
      (canonical s f).act ≫ e.hom

/-- The involution `(a, b) ↦ (act (a, b), x' a)` of `X' ×_S S'` defined by an action. -/
private noncomputable def invol {X' : Scheme.{u}} {x' : X' ⟶ S'} (A : DescentAction s x') :
    pullback (x' ≫ s) s ⟶ pullback (x' ≫ s) s :=
  pullback.lift A.act (pullback.fst _ _ ≫ x')
    (by rw [reassoc_of% A.act_comp, Category.assoc]; exact pullback.condition.symm)

section invol

variable {X' : Scheme.{u}} {x' : X' ⟶ S'} (A : DescentAction s x')

@[reassoc (attr := simp)]
private theorem invol_fst : invol A ≫ pullback.fst _ _ = A.act :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem invol_snd : invol A ≫ pullback.snd _ _ = pullback.fst _ _ ≫ x' :=
  pullback.lift_snd _ _ _

private theorem toTriple_actMap : toTriple s x' ≫ actMap A.act A.act_comp = invol A := by
  apply pullback.hom_ext
  · rw [Category.assoc, actMap_fst, toTriple_fst_assoc, invol_fst]
  · rw [Category.assoc, actMap_snd, toTriple_snd, invol_snd]

@[reassoc (attr := simp)]
private theorem invol_act : invol A ≫ A.act = pullback.fst _ _ := by
  rw [← toTriple_actMap, Category.assoc, A.trans, ← Category.assoc, toTriple_proj₁₃,
    Category.assoc, A.unit_act, Category.comp_id]

@[reassoc (attr := simp)]
private theorem invol_invol : invol A ≫ invol A = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, invol_fst, invol_act, Category.id_comp]
  · rw [Category.assoc, invol_snd, invol_fst_assoc, A.act_comp, Category.id_comp]

private instance : IsIso (invol A) := ⟨⟨invol A, invol_invol A, invol_invol A⟩⟩

private theorem act_eq_invol_fst : A.act = invol A ≫ pullback.fst _ _ := (invol_fst A).symm

private theorem hom_ext' {T : Scheme.{u}} {a b : T ⟶ pullback (x' ≫ s) s}
    (h₁ : a ≫ pullback.fst _ _ = b ≫ pullback.fst _ _) (h₂ : a ≫ A.act = b ≫ A.act) : a = b := by
  apply pullback.hom_ext h₁
  rw [← A.act_comp, reassoc_of% h₂]

private theorem equivalence (T : Scheme.{u}) :
    _root_.Equivalence fun x y : T ⟶ X' =>
      ∃ φ : T ⟶ pullback (x' ≫ s) s, φ ≫ pullback.fst _ _ = x ∧ φ ≫ A.act = y where
  refl x := ⟨x ≫ unitMap s x', by rw [Category.assoc, unitMap_fst, Category.comp_id],
    by rw [Category.assoc, A.unit_act, Category.comp_id]⟩
  symm := by
    rintro x y ⟨φ, hφ, hφ'⟩
    exact ⟨φ ≫ invol A, by rw [Category.assoc, invol_fst, hφ'],
      by rw [Category.assoc, invol_act, hφ]⟩
  trans := by
    rintro x y z ⟨φ, hφ, hφ'⟩ ⟨ψ, hψ, hψ'⟩
    have w : φ ≫ pullback.snd (x' ≫ s) s ≫ s = (ψ ≫ pullback.snd (x' ≫ s) s) ≫ s := by
      rw [Category.assoc, ← pullback.condition, reassoc_of% hψ, ← reassoc_of% hφ',
        reassoc_of% A.act_comp, pullback.condition]
    let k : T ⟶ pullback (pullback.snd (x' ≫ s) s ≫ s) s :=
      pullback.lift φ (ψ ≫ pullback.snd _ _) w
    have hk₁ : k ≫ actMap A.act A.act_comp = ψ := by
      apply pullback.hom_ext
      · rw [Category.assoc, actMap_fst, pullback.lift_fst_assoc, hφ', hψ]
      · rw [Category.assoc, actMap_snd, pullback.lift_snd]
    refine ⟨k ≫ proj₁₃ s x', by rw [Category.assoc, proj₁₃_fst, pullback.lift_fst_assoc, hφ], ?_⟩
    rw [Category.assoc, ← A.trans, ← Category.assoc, hk₁, hψ']

end invol

/-- If the graph of a descent action `A` is the kernel pair of a flat, surjective,
quasi-compact `p : X' ⟶ Y` and `f : Y ⟶ S` satisfies `p ≫ f = x' ≫ s`, then
`(p, x') : X' ⟶ Y ×_S S'` is an isomorphism identifying `A` with the canonical action. -/
public theorem effective_of_isPullback_of_flat_surjective
    {S S' : Scheme.{u}} (s : S' ⟶ S) {X' : Scheme.{u}} {x' : X' ⟶ S'} (A : DescentAction s x')
    {Y : Scheme.{u}} (p : X' ⟶ Y) [Flat p] [Surjective p] [QuasiCompact p]
    (w : pullback.fst (x' ≫ s) s ≫ p = A.act ≫ p)
    (hR : IsPullback (pullback.fst (x' ≫ s) s) A.act p p)
    (f : Y ⟶ S) (hpf : p ≫ f = x' ≫ s) :
    ∃ (e : pullback f s ≅ X') (he : e.hom ≫ x' = pullback.snd f s),
      e.inv = pullback.lift p x' hpf ∧
      pullback.map (pullback.snd f s ≫ s) s (x' ≫ s) s e.hom (𝟙 S') (𝟙 S)
          (by rw [Category.comp_id, ← Category.assoc, he])
          (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
        (DescentAction.canonical s f).act ≫ e.hom := by
  set u : X' ⟶ pullback f s := pullback.lift p x' hpf
  have hu₁ : u ≫ pullback.fst f s = p := pullback.lift_fst _ _ _
  have hu₂ : u ≫ pullback.snd f s = x' := pullback.lift_snd _ _ _
  let c : pullback (x' ≫ s) s ⟶ pullback f s :=
    pullback.lift (pullback.fst (x' ≫ s) s ≫ p) (pullback.snd (x' ≫ s) s)
      (by rw [Category.assoc, hpf]; exact pullback.condition)
  have hc₁ : c ≫ pullback.fst f s = pullback.fst (x' ≫ s) s ≫ p := pullback.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd f s = pullback.snd (x' ≫ s) s := pullback.lift_snd _ _ _
  have big : IsPullback (pullback.fst (x' ≫ s) s) (c ≫ pullback.snd f s) (p ≫ f) s := by
    rw [hc₂, hpf]
    exact IsPullback.of_hasPullback (x' ≫ s) s
  have sq₁ : IsPullback (pullback.fst (x' ≫ s) s) c p (pullback.fst f s) :=
    big.of_bot hc₁.symm (IsPullback.of_hasPullback f s)
  have hQc : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) c :=
    ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) sq₁ inferInstance,
      MorphismProperty.of_isPullback (P := @Flat) sq₁ inferInstance⟩,
      MorphismProperty.of_isPullback (P := @QuasiCompact) sq₁ inferInstance⟩
  have key : ∀ {T : Scheme.{u}} (a : T ⟶ pullback (x' ≫ s) s) (b : T ⟶ X'),
      a ≫ c = b ≫ u → a ≫ A.act = b := by
    intro T a b h
    have h₁ : (a ≫ pullback.fst (x' ≫ s) s) ≫ p = b ≫ p := by
      rw [Category.assoc, ← hc₁, ← Category.assoc, h, Category.assoc, hu₁]
    have h₂ : a ≫ pullback.snd (x' ≫ s) s = b ≫ x' := by
      rw [← hc₂, ← Category.assoc, h, Category.assoc, hu₂]
    have hφ : hR.lift (a ≫ pullback.fst (x' ≫ s) s) b h₁ = a := by
      apply pullback.hom_ext
      · rw [hR.lift_fst]
      · rw [h₂, ← A.act_comp, ← Category.assoc, hR.lift_snd]
    rw [← hφ, hR.lift_snd]
  have comm : 𝟙 (pullback (x' ≫ s) s) ≫ c = A.act ≫ u := by
    rw [Category.id_comp]
    apply pullback.hom_ext
    · rw [hc₁, Category.assoc, hu₁, w]
    · rw [hc₂, Category.assoc, hu₂, A.act_comp]
  have sq₂ : IsPullback (𝟙 (pullback (x' ≫ s) s)) A.act c u :=
    IsPullback.of_iso_pullback ⟨comm⟩
      { hom := pullback.lift (𝟙 _) A.act comm
        inv := pullback.fst c u
        hom_inv_id := pullback.lift_fst _ _ _
        inv_hom_id := by
          apply pullback.hom_ext
          · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
          · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
            exact key _ _ pullback.condition }
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have hiso : (MorphismProperty.isomorphisms Scheme.{u}) u :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme.{u})
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq₂ hQc
      ((MorphismProperty.isomorphisms.iff _).mpr inferInstance)
  have : IsIso u := (MorphismProperty.isomorphisms.iff _).mp hiso
  have hinv₁ : inv u ≫ p = pullback.fst f s := by rw [IsIso.inv_comp_eq, hu₁]
  have hinv₂ : inv u ≫ x' = pullback.snd f s := by rw [IsIso.inv_comp_eq, hu₂]
  have compat : ∀ m : pullback (pullback.snd f s ≫ s) s ⟶ pullback (x' ≫ s) s,
      m ≫ pullback.fst (x' ≫ s) s = pullback.fst _ _ ≫ inv u →
        m ≫ pullback.snd (x' ≫ s) s = pullback.snd _ _ →
          m ≫ A.act = DescentAction.flipMap s f ≫ inv u := by
    intro m hm₁ hm₂
    rw [IsIso.eq_comp_inv, Category.assoc]
    apply pullback.hom_ext
    · simp only [Category.assoc, hu₁]
      rw [← w, reassoc_of% hm₁, hinv₁, DescentAction.flipMap_fst]
    · simp only [Category.assoc, hu₂]
      rw [A.act_comp, hm₂, DescentAction.flipMap_snd]
  have he : (asIso u).symm.hom ≫ x' = pullback.snd f s := hinv₂
  refine ⟨(asIso u).symm, he, rfl, ?_⟩
  exact compat _ (pullback.lift_fst _ _ _) ((pullback.lift_snd _ _ _).trans (Category.comp_id _))

/-- A descent action along a finite, flat, finitely presented `φ` on a scheme in which
every finite set of points lies in an affine open is effective; `φ` need not be surjective. -/
public theorem effective_of_finiteLocallyFree
    {S S' : Scheme.{u}} (φ : S' ⟶ S) [IsFinite φ] [Flat φ] [LocallyOfFinitePresentation φ]
    {X' : Scheme.{u}} {x' : X' ⟶ S'} (A : DescentAction φ x')
    (haff : ∀ F : Finset X', ∃ U : X'.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) :
    A.Effective := by
  have : IsFinite A.act := by rw [act_eq_invol_fst]; infer_instance
  have : Flat A.act := by rw [act_eq_invol_fst]; infer_instance
  have : LocallyOfFinitePresentation A.act := by rw [act_eq_invol_fst]; infer_instance
  have haff' : ∀ x : X', ∃ U : X'.Opens, IsAffineOpen U ∧
      ∀ r : ↑(pullback (x' ≫ φ) φ), pullback.fst (x' ≫ φ) φ r = x → A.act r ∈ U := by
    intro x
    have hfinite := (pullback.fst (x' ≫ φ) φ).finite_preimage_singleton x
    obtain ⟨U, hU, hSU⟩ := haff ((hfinite.image fun r => A.act r).toFinset)
    exact ⟨U, hU, fun r hr => hSU _ (by
      rw [Set.Finite.mem_toFinset]
      exact ⟨r, by simpa using hr, rfl⟩)⟩
  obtain ⟨Y, p, w, hpfin, hpflat, -, hpsurj, hR, ⟨hcolim⟩⟩ :=
    Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation
      (pullback.fst (x' ≫ φ) φ) A.act (fun a b h₁ h₂ => hom_ext' A h₁ h₂)
      (fun T => equivalence A T) haff'
  have := hpfin
  have := hpflat
  have := hpsurj
  have hco : pullback.fst (x' ≫ φ) φ ≫ x' ≫ φ = A.act ≫ x' ≫ φ := by
    rw [pullback.condition, reassoc_of% A.act_comp]
  obtain ⟨f, hpf⟩ := Cofork.IsColimit.desc' hcolim (x' ≫ φ) hco
  obtain ⟨e, he, -, hc⟩ := effective_of_isPullback_of_flat_surjective φ A p w hR f hpf
  exact ⟨Y, f, e, he, hc⟩

-- The proof uses only that `R'` is finite, flat and finitely presented
-- (`effective_of_finiteLocallyFree`); faithful flatness is kept from the source statement.
/-- Along `Spec R' ⟶ Spec R` for a finite étale faithfully flat `R`-algebra `R'`, every
descent action on a scheme `X'` in which each finite set of points lies in an affine open
is effective. -/
@[nolint unusedArguments]
public theorem effective_of_finiteEtale
    (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    {X' : Scheme.{u}} {x' : X' ⟶ Spec (CommRingCat.of R')}
    (A : DescentAction (Spec.map (CommRingCat.ofHom (algebraMap R R'))) x')
    (haff : ∀ S : Finset X', ∃ U : X'.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U) :
    A.Effective := by
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (by
      change RingHom.Flat (algebraMap R R')
      exact RingHom.flat_algebraMap_iff.2 inferInstance)
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    (IsFinite.SpecMap_iff _).2 (by
      change (algebraMap R R').Finite
      exact RingHom.finite_algebraMap.mpr inferInstance)
  have : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2 (by
      change (algebraMap R R').FinitePresentation
      exact RingHom.finitePresentation_algebraMap.mpr inferInstance)
  exact effective_of_finiteLocallyFree _ A haff

end DescentAction

end AlgebraicGeometry
