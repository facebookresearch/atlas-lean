/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Coproducts of simplicial sets: elements, pullbacks, inner fibrations

Neutral coproduct infrastructure for `SSet`, in the presheaf topos:
degreewise a coproduct is a Sigma type (`SSet.sigmaObjEquiv`),
coproducts of pullback squares are pullbacks, pullbacks along a
map out of a coproduct are coproducts of pullbacks
(universality), the component inclusions into a coproduct of maps
are pullbacks (disjointness), and coproducts of monomorphisms and
of inner fibrations are monomorphisms and inner fibrations. None
of the signatures involve selective towers or Stevenson's
construction; the Proposition 4.7 consumer lives in
[SelectiveTower.lean](SelectiveTower.lean).
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace SSet

/-! ### Elements of coproducts of simplicial sets

Coproducts in `SSet` are universal and disjoint, as in any
presheaf topos: degreewise they are Sigma types. The bridge is
`SSet.sigmaObjEquiv`, assembled from preservation of colimits by
evaluation and `Types.coproductIso`. -/

section SigmaElements

variable {ι : Type u} {F G : ι → SSet.{u}}

/-- Element form of a composition equality in a degree: if
`α ≫ β = γ` then `β` applied after `α` in degree `k` is `γ`. -/
private theorem app_comp_apply_eq {A B C : SSet.{u}} {α : A ⟶ B}
    {β : B ⟶ C} {γ : A ⟶ C} (H : α ≫ β = γ) (k : ℕ) (x : A _⦋k⦌) :
    (β.app (op ⦋k⦌)) ((α.app (op ⦋k⦌)) x) = (γ.app (op ⦋k⦌)) x := by
  have h := types_congr_hom (congrArg (fun t => t.app (op ⦋k⦌)) H) x
  rwa [NatTrans.comp_app, types_comp_apply] at h

/-- The degree-`k` simplices of a coproduct of simplicial sets are
the Sigma type of the degree-`k` simplices of the components:
evaluation at `⦋k⦌` preserves the coproduct, and in `Type u` the
coproduct is the Sigma type (`Types.coproductIso`). -/
noncomputable def sigmaObjEquiv (F : ι → SSet.{u}) (k : ℕ) :
    (∐ F : SSet.{u}) _⦋k⦌ ≃ Σ c, (F c) _⦋k⦌ :=
  (preservesColimitIso ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋k⦌))
      (Discrete.functor F) ≪≫
    HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete F _) ≪≫
    Types.coproductIso (fun c => (F c).obj (op ⦋k⦌))).toEquiv

/-- Under `SSet.sigmaObjEquiv`, a simplex coming from component
`c` maps to the Sigma pair `⟨c, -⟩`. -/
theorem sigmaObjEquiv_ι_app (k : ℕ) (c : ι) (y : (F c) _⦋k⦌) :
    sigmaObjEquiv F k ((Sigma.ι F c).app (op ⦋k⦌) y) = ⟨c, y⟩ := by
  let E := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋k⦌)
  have key1 : (Sigma.ι F c).app (op ⦋k⦌) ≫
        (preservesColimitIso E (Discrete.functor F)).hom =
      colimit.ι (Discrete.functor F ⋙ E) ⟨c⟩ :=
    ι_preservesColimitIso_hom E (Discrete.functor F) ⟨c⟩
  have key2 : colimit.ι (Discrete.functor F ⋙ E) ⟨c⟩ ≫
        (HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete F E)).hom =
      Sigma.ι (fun c => (F c).obj (op ⦋k⦌)) c := by
    rw [HasColimit.ι_isoOfNatIso_hom]
    simp only [Discrete.compNatIsoDiscrete, Discrete.natIso]
    rfl
  have key3 : (Sigma.ι F c).app (op ⦋k⦌) ≫
        (preservesColimitIso E (Discrete.functor F) ≪≫
          HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete F E) ≪≫
          Types.coproductIso (fun c => (F c).obj (op ⦋k⦌))).hom =
      ↾(fun y => (⟨c, y⟩ : Σ c, (F c) _⦋k⦌)) := by
    rw [Iso.trans_hom, Iso.trans_hom, ← Category.assoc, ← Category.assoc,
      key1, key2, Types.coproductIso_ι_comp_hom]
  have h := types_congr_hom key3 y
  rwa [types_comp_apply] at h

/-- Every simplex of a coproduct of simplicial sets comes from a
simplex of a unique component (joint surjectivity, from
`SSet.sigmaObjEquiv`). -/
theorem exists_sigma_ι_app_eq (k : ℕ) (x : (∐ F : SSet.{u}) _⦋k⦌) :
    ∃ (c : ι) (y : (F c) _⦋k⦌), (Sigma.ι F c).app (op ⦋k⦌) y = x := by
  refine ⟨(sigmaObjEquiv F k x).1, (sigmaObjEquiv F k x).2, ?_⟩
  apply (sigmaObjEquiv F k).injective
  rw [sigmaObjEquiv_ι_app]

/-- Coproducts of simplicial sets are disjoint on components: if
simplices from components `c` and `c'` become equal in the
coproduct, then `c = c'`. -/
theorem eq_of_sigma_ι_app_eq {k : ℕ} {c c' : ι} {y : (F c) _⦋k⦌}
    {y' : (F c') _⦋k⦌}
    (h : (Sigma.ι F c).app (op ⦋k⦌) y = (Sigma.ι F c').app (op ⦋k⦌) y') :
    c = c' := by
  have h2 := congrArg (fun p : Σ c, (F c) _⦋k⦌ => p.1)
    (congrArg (sigmaObjEquiv F k) h)
  rwa [sigmaObjEquiv_ι_app, sigmaObjEquiv_ι_app] at h2

/-- The coproduct injections of simplicial sets are degreewise
injective. -/
theorem injective_sigma_ι_app (k : ℕ) (c : ι) :
    Function.Injective ((Sigma.ι F c).app (op ⦋k⦌)) := by
  intro y₁ y₂ h
  have h2 := congrArg (sigmaObjEquiv F k) h
  rw [sigmaObjEquiv_ι_app, sigmaObjEquiv_ι_app] at h2
  exact eq_of_heq (Sigma.mk.inj_iff.mp h2).2

/-- A coproduct map `Limits.Sigma.map q` acts on a simplex from
component `c` as `q c` followed by the component inclusion
(`Limits.Sigma.ι_map` at elements). -/
theorem sigmaMap_app_ι_app (q : ∀ c, F c ⟶ G c) (k : ℕ) (c : ι)
    (y : (F c) _⦋k⦌) :
    (Limits.Sigma.map q).app (op ⦋k⦌) ((Sigma.ι F c).app (op ⦋k⦌) y) =
      (Sigma.ι G c).app (op ⦋k⦌) ((q c).app (op ⦋k⦌) y) :=
  app_comp_apply_eq (Sigma.ι_map q c) k y

/-- A map `Limits.Sigma.desc f` out of a coproduct acts on a
simplex from component `c` as `f c` (`Limits.Sigma.ι_comp_desc`
at elements). -/
theorem sigmaDesc_app_ι_app {Z : SSet.{u}} (f : ∀ c, F c ⟶ Z)
    (k : ℕ) (c : ι) (y : (F c) _⦋k⦌) :
    (Sigma.desc f).app (op ⦋k⦌) ((Sigma.ι F c).app (op ⦋k⦌) y) =
      (f c).app (op ⦋k⦌) y :=
  app_comp_apply_eq (Sigma.ι_comp_desc f c) k y

/-- A coproduct of monomorphisms of simplicial sets is a
monomorphism: the generic `MorphismProperty` coproduct stability
for `SSet` (`MorphismProperty.colimMap` with the
`IsStableUnderCoproducts` instance for `monomorphisms SSet`). -/
theorem mono_sigmaMap (f : ∀ c, F c ⟶ G c) (hf : ∀ c, Mono (f c)) :
    Mono (Limits.Sigma.map f) := by
  have h : (MorphismProperty.monomorphisms SSet.{u})
      (Limits.Sigma.map f) := by
    apply MorphismProperty.colimMap
      (W := MorphismProperty.monomorphisms SSet.{u})
    rintro ⟨c⟩
    exact hf c
  exact h

end SigmaElements

/-! ### Pullback squares over coproducts

The three coproduct facts of the presheaf topos consumed by
Proposition 4.7's one-step construction, each proved degreewise
via the helper below and the element API above: coproducts of
pullback squares are pullbacks; pullbacks along a map out of a
coproduct are coproducts of pullbacks (universality); the
component inclusions into a coproduct of maps are pullbacks
(disjointness). -/

section SigmaPullbacks

variable {ι : Type u} {A B : ι → SSet.{u}}

/-- Pullback squares of simplicial sets are detected in each
degree: if the evaluated square in `Type u` is a pullback for
every `n`, the original square is a pullback. This mirrors
`SSet.isPullback_of_isPullback_app` in DescentProp412.lean
(Mathlib's `IsPullback.of_forall_isPullback_app` plus the
observation that every object of `SimplexCategoryᵒᵖ` is `op ⦋n⦌`
for some `n`); it is inlined here so this module depends only on
Mathlib. -/
private theorem isPullback_of_isPullback_app {X Y S T : SSet.{u}}
    {g : X ⟶ Y} {p : X ⟶ S} {q : Y ⟶ T} {f : S ⟶ T}
    (h : ∀ n : ℕ, IsPullback (g.app (op ⦋n⦌)) (p.app (op ⦋n⦌))
      (q.app (op ⦋n⦌)) (f.app (op ⦋n⦌))) :
    IsPullback g p q f :=
  IsPullback.of_forall_isPullback_app (fun k ↦ by
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = op ⦋n⦌ := ⟨k.unop.len, by simp⟩
    exact h n)

/-- Element form of `NatTrans.comp_app`. -/
private theorem app_comp {X Y Z : SSet.{u}} (α : X ⟶ Y) (β : Y ⟶ Z)
    (k : ℕ) (x : X _⦋k⦌) :
    ((α ≫ β).app (op ⦋k⦌)) x =
      (β.app (op ⦋k⦌)) ((α.app (op ⦋k⦌)) x) := by
  rw [NatTrans.comp_app, types_comp_apply]

/-- **Coproducts of pullback squares are pullbacks** in `SSet`.
Degreewise: a simplex of the coproduct source lies in one
component, where the component pullback supplies existence and
uniqueness; disjointness (`SSet.eq_of_sigma_ι_app_eq`) forces the
two sides of a lifting datum into the same component. -/
theorem isPullback_sigmaMap {X Y Z W : ι → SSet.{u}}
    (t : ∀ c, X c ⟶ Y c) (l : ∀ c, X c ⟶ Z c) (r : ∀ c, Y c ⟶ W c)
    (b : ∀ c, Z c ⟶ W c) (h : ∀ c, IsPullback (t c) (l c) (r c) (b c)) :
    IsPullback (Limits.Sigma.map t) (Limits.Sigma.map l)
      (Limits.Sigma.map r) (Limits.Sigma.map b) := by
  apply isPullback_of_isPullback_app
  intro k
  let E := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋k⦌)
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro x
    obtain ⟨c, y, rfl⟩ := exists_sigma_ι_app_eq k x
    simp only [types_comp_apply, sigmaMap_app_ι_app]
    rw [app_comp_apply_eq (h c).w k y, app_comp]
  · intro x₁ x₂ hx
    obtain ⟨c₁, y₁, rfl⟩ := exists_sigma_ι_app_eq k x₁
    obtain ⟨c₂, y₂, rfl⟩ := exists_sigma_ι_app_eq k x₂
    simp only [sigmaMap_app_ι_app] at hx
    obtain rfl : c₁ = c₂ := eq_of_sigma_ι_app_eq hx.1
    have h1 : (t c₁).app (op ⦋k⦌) y₁ = (t c₁).app (op ⦋k⦌) y₂ :=
      injective_sigma_ι_app k c₁ hx.1
    have h2 : (l c₁).app (op ⦋k⦌) y₁ = (l c₁).app (op ⦋k⦌) y₂ :=
      injective_sigma_ι_app k c₁ hx.2
    rw [Types.ext_of_isPullback ((h c₁).map E) h1 h2]
  · intro x₂ x₃ hx
    obtain ⟨c₂, y₂, rfl⟩ := exists_sigma_ι_app_eq k x₂
    obtain ⟨c₃, y₃, rfl⟩ := exists_sigma_ι_app_eq k x₃
    simp only [sigmaMap_app_ι_app] at hx
    obtain rfl : c₂ = c₃ := eq_of_sigma_ι_app_eq hx
    have h2 : (r c₂).app (op ⦋k⦌) y₂ = (b c₂).app (op ⦋k⦌) y₃ :=
      injective_sigma_ι_app k c₂ hx
    obtain ⟨y, hy1, hy2⟩ :=
      Types.exists_of_isPullback ((h c₂).map E) y₂ y₃ h2
    have hy1' : (t c₂).app (op ⦋k⦌) y = y₂ := hy1
    have hy2' : (l c₂).app (op ⦋k⦌) y = y₃ := hy2
    exact ⟨(Sigma.ι X c₂).app (op ⦋k⦌) y,
      by rw [sigmaMap_app_ι_app, hy1'], by rw [sigmaMap_app_ι_app, hy2']⟩

/-- **Universality of coproducts in `SSet`**: the square
exhibiting `∐_c (Z ×_X Λ_c)` as the pullback of `pz : Z ⟶ X`
along `Sigma.desc α : ∐ Λ ⟶ X` is a pullback. Degreewise this is
the set-theoretic fact that a pair `(z, ⟨c, s⟩)` with
`pz z = α_c s` is a unique element of the component pullback. -/
theorem isPullback_sigmaDesc_fst_map_snd {Z X : SSet.{u}}
    (pz : Z ⟶ X) {Λ : ι → SSet.{u}} (α : ∀ c, Λ c ⟶ X) :
    IsPullback (Sigma.desc fun c => pullback.fst pz (α c))
      (Limits.Sigma.map fun c => pullback.snd pz (α c)) pz
      (Sigma.desc α) := by
  apply isPullback_of_isPullback_app
  intro k
  let E := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋k⦌)
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro x
    obtain ⟨c, y, rfl⟩ := exists_sigma_ι_app_eq k x
    simp only [types_comp_apply, sigmaDesc_app_ι_app, sigmaMap_app_ι_app]
    rw [app_comp_apply_eq (pullback.condition (f := pz) (g := α c)) k y,
      app_comp]
  · intro x₁ x₂ hx
    obtain ⟨c₁, y₁, rfl⟩ := exists_sigma_ι_app_eq k x₁
    obtain ⟨c₂, y₂, rfl⟩ := exists_sigma_ι_app_eq k x₂
    simp only [sigmaDesc_app_ι_app, sigmaMap_app_ι_app] at hx
    obtain rfl : c₁ = c₂ := eq_of_sigma_ι_app_eq hx.2
    have h2 : (pullback.snd pz (α c₁)).app (op ⦋k⦌) y₁ =
        (pullback.snd pz (α c₁)).app (op ⦋k⦌) y₂ :=
      injective_sigma_ι_app k c₁ hx.2
    rw [Types.ext_of_isPullback
      ((IsPullback.of_hasPullback pz (α c₁)).map E) hx.1 h2]
  · intro x₂ x₃ hx
    obtain ⟨c₃, y₃, rfl⟩ := exists_sigma_ι_app_eq k x₃
    rw [sigmaDesc_app_ι_app] at hx
    obtain ⟨y, hy1, hy2⟩ := Types.exists_of_isPullback
      ((IsPullback.of_hasPullback pz (α c₃)).map E) x₂ y₃ hx
    have hy1' : (pullback.fst pz (α c₃)).app (op ⦋k⦌) y = x₂ := hy1
    have hy2' : (pullback.snd pz (α c₃)).app (op ⦋k⦌) y = y₃ := hy2
    exact ⟨(Sigma.ι (fun c => pullback pz (α c)) c₃).app (op ⦋k⦌) y,
      by rw [sigmaDesc_app_ι_app, hy1'],
      by rw [sigmaMap_app_ι_app, hy2']⟩

/-- **Disjointness of coproducts in `SSet`**: pulling a coproduct
map `∐ q` back along a component inclusion `Sigma.ι B c` returns
the component `q c`. -/
theorem isPullback_sigma_ι_sigmaMap (q : ∀ c, A c ⟶ B c) (c : ι) :
    IsPullback (Sigma.ι A c) (q c) (Limits.Sigma.map q) (Sigma.ι B c) := by
  apply isPullback_of_isPullback_app
  intro k
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro y
    simp only [types_comp_apply, sigmaMap_app_ι_app]
  · intro x₁ x₂ hx
    exact injective_sigma_ι_app k c hx.1
  · intro x₂ x₃ hx
    obtain ⟨c', y, rfl⟩ := exists_sigma_ι_app_eq k x₂
    rw [sigmaMap_app_ι_app] at hx
    obtain rfl : c = c' := (eq_of_sigma_ι_app_eq hx).symm
    exact ⟨y, rfl, injective_sigma_ι_app k c hx⟩

end SigmaPullbacks

/-! ### Coproducts of inner fibrations

A coproduct of inner fibrations is an inner fibration: the bottom
simplex of a horn lifting problem lies in one component (maps out
of a representable factor through coproduct components), and the
disjointness square `SSet.isPullback_sigma_ι_sigmaMap` pulls the
whole problem back to that component. -/

section SigmaInnerFibration

variable {ι : Type u} {A B : ι → SSet.{u}}

/-- A map out of a standard simplex into a coproduct of
simplicial sets factors through one component: its classifying
simplex does (`SSet.exists_sigma_ι_app_eq`). -/
theorem exists_sigma_ι_comp_eq {F : ι → SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ ∐ F) :
    ∃ (c : ι) (β : (Δ[m] : SSet.{u}) ⟶ F c), β ≫ Sigma.ι F c = f := by
  obtain ⟨c, b, hb⟩ := exists_sigma_ι_app_eq m (yonedaEquiv f)
  refine ⟨c, yonedaEquiv.symm b, ?_⟩
  simp only [yonedaEquiv_symm_comp, hb, Equiv.symm_apply_apply]

set_option linter.style.haveILetI false in
/-- Horn lifting against a coproduct of inner fibrations: the
bottom simplex lies in one component
(`SSet.exists_sigma_ι_comp_eq`), and the disjointness pullback
`SSet.isPullback_sigma_ι_sigmaMap` reduces the problem to that
component. -/
theorem hasLiftingProperty_horn_sigmaMap (q : ∀ c, A c ⟶ B c)
    (hq : ∀ c, InnerFibration (q c)) {n : ℕ} {i : Fin (n + 3)}
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) :
    HasLiftingProperty Λ[n + 2, i].ι (Limits.Sigma.map q) where
  sq_hasLift {top bottom} hsq := by
    obtain ⟨c, β, hβ⟩ := exists_sigma_ι_comp_eq bottom
    let sq := isPullback_sigma_ι_sigmaMap q c
    have hw : top ≫ Limits.Sigma.map q =
        (Λ[n + 2, i].ι ≫ β) ≫ Sigma.ι B c := by
      rw [Category.assoc, hβ]
      exact hsq.w
    let top' : (Λ[n + 2, i] : SSet.{u}) ⟶ A c :=
      sq.lift top (Λ[n + 2, i].ι ≫ β) hw
    have h1 : top' ≫ Sigma.ι A c = top := sq.lift_fst _ _ _
    have h2 : top' ≫ q c = Λ[n + 2, i].ι ≫ β := sq.lift_snd _ _ _
    haveI := hq c
    have hlift : HasLiftingProperty Λ[n + 2, i].ι (q c) :=
      InnerFibration.mem _ (horn_ι_mem_innerHornInclusions h0 hn)
    let sq₁ : CommSq top' Λ[n + 2, i].ι (q c) β := CommSq.mk h2
    refine CommSq.HasLift.mk' ⟨sq₁.lift ≫ Sigma.ι A c, ?_, ?_⟩
    · rw [← Category.assoc, sq₁.fac_left, h1]
    · rw [Category.assoc, sq.w, ← Category.assoc, sq₁.fac_right, hβ]

/-- **A coproduct of inner fibrations is an inner fibration**
(degreewise disjointness and universality of coproducts in the
presheaf topos; cf. `SSet.hasLiftingProperty_horn_sigmaMap`). -/
theorem innerFibration_sigmaMap (q : ∀ c, A c ⟶ B c)
    (hq : ∀ c, InnerFibration (q c)) :
    InnerFibration (Limits.Sigma.map q) where
  mem := by
    intro _ _ g hg
    obtain ⟨i, h0, hn⟩ := hg
    exact hasLiftingProperty_horn_sigmaMap q hq h0 hn

end SigmaInnerFibration

end SSet

end
