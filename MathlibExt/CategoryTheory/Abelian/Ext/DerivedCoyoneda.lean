/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
Authors: @junekim623, @toskua
-/

module

public import Mathlib.Algebra.Homology.ComplexShape
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.Algebra.Homology.ShortComplex.LeftHomology
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import MathlibExt.CategoryTheory.Abelian.Injective.ResolutionComparison

/-!
# Right-derived Coyoneda functors and Ext

In an abelian category with injective resolutions, the right-derived functors of
`preadditiveCoyoneda.obj (Opposite.op X)` identify with the groups `Abelian.Ext X Y n`.
The comparison uses an injective resolution of `Y` and is natural in `Y` under postcomposition
with `Ext.mk₀`. The Ext universe is the morphism universe of the category, matching the
additive-group target of Coyoneda. The resulting natural isomorphism has target
`Abelian.extFunctorObj`.
-/

/-
Authorship of the adapted portions: @toskua, @junekim623.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace CategoryTheory.DerivedCoyoneda

variable (X : C) {Y : C} (R : InjectiveResolution Y) (n : ℕ)

/-- The complex computing the right-derived functors: `preadditiveCoyoneda`
applied to an injective resolution. Its degree-`n` term is the group of
morphisms `X ⟶ R.cocomplex.X n`, with postcomposition differentials.

This is an `abbrev` (reducible) rather than a `def` so that rewrites of index
equalities never see a semireducible unfolding in their motive: all dependent
motive checks below run at `implicit` transparency. -/
noncomputable abbrev mappedCocomplex : CochainComplex AddCommGrpCat.{v} ℕ :=
  ((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex _).obj
    R.cocomplex

/-- Cocycles for the comparison: morphisms `X ⟶ R.cocomplex.X n` killed by the
next differential of the resolution. -/
def cocycleSubgroup : AddSubgroup (X ⟶ R.cocomplex.X n) where
  carrier := {f | f ≫ R.cocomplex.d n (n + 1) = 0}
  add_mem' := fun {a b} ha hb => by
    have ha' : a ≫ R.cocomplex.d n (n + 1) = 0 := ha
    have hb' : b ≫ R.cocomplex.d n (n + 1) = 0 := hb
    change (a + b) ≫ R.cocomplex.d n (n + 1) = 0
    rw [Preadditive.add_comp, ha', hb', add_zero]
  zero_mem' := by
    change (0 : X ⟶ R.cocomplex.X n) ≫ R.cocomplex.d n (n + 1) = 0
    rw [zero_comp]
  neg_mem' := fun {a} ha => by
    have ha' : a ≫ R.cocomplex.d n (n + 1) = 0 := ha
    change (-a) ≫ R.cocomplex.d n (n + 1) = 0
    rw [_root_.CategoryTheory.Preadditive.neg_comp, ha', neg_zero]

/-- The group of cocycles as an object of `AddCommGrpCat`. -/
def cocyclesObj : AddCommGrpCat.{v} :=
  AddCommGrpCat.of (cocycleSubgroup X R n)

/-- The differential out of degree `n` acts by postcomposition. The right-hand
side is stated with plain type ascriptions (which are transparent to
rewriting) rather than `show ... from ...` (which is not). -/
lemma sc_g_apply (y : ↥(((mappedCocomplex X R).sc n).X₂)) :
    ((mappedCocomplex X R).sc n).g y =
      (((y : X ⟶ R.cocomplex.X n) ≫
        R.cocomplex.d n ((ComplexShape.up ℕ).next n) :
        X ⟶ R.cocomplex.X ((ComplexShape.up ℕ).next n)) :
        ↥(((mappedCocomplex X R).sc n).X₃)) := rfl

/-- The differential into degree `n` acts by postcomposition. -/
lemma sc_f_apply (t : ↥(((mappedCocomplex X R).sc n).X₁)) :
    ((mappedCocomplex X R).sc n).f t =
      (((t : X ⟶ R.cocomplex.X ((ComplexShape.up ℕ).prev n)) ≫
        R.cocomplex.d ((ComplexShape.up ℕ).prev n) n :
        X ⟶ R.cocomplex.X n) :
        ↥(((mappedCocomplex X R).sc n).X₂)) := rfl

/-- The inclusion of cocycles into the degree-`n` term. -/
def cocycleInclusion :
    cocyclesObj X R n ⟶ ((mappedCocomplex X R).sc n).X₂ :=
  AddCommGrpCat.ofHom
    { toFun := fun c ↦ ((c.val : X ⟶ R.cocomplex.X n) :
        ↥(((mappedCocomplex X R).sc n).X₂))
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- The inclusion lands in cycles. The index equality is rewritten in the
pure-`C` hypothesis (never in the goal, whose `X₃` type depends on it). -/
lemma cocycle_wi :
    cocycleInclusion X R n ≫ ((mappedCocomplex X R).sc n).g = 0 := by
  apply AddCommGrpCat.ext
  intro x
  change ((mappedCocomplex X R).sc n).g ((cocycleInclusion X R n) x) = 0
  have hx : (x.val : X ⟶ R.cocomplex.X n) ≫ R.cocomplex.d n (n + 1) = 0 :=
    x.property
  have hnext : (ComplexShape.up ℕ).next n = n + 1 :=
    ComplexShape.next_eq' _ (ComplexShape.up_mk _ _ rfl)
  have hg := sc_g_apply X R n ((cocycleInclusion X R n) x)
  rw [hg]
  rw [← hnext] at hx
  exact hx

/-- The cocycles are the kernel of the outgoing differential. As above, the
index equality is rewritten in a pure-`C` intermediary, not in a hypothesis
whose type mentions the mapped complex. -/
noncomputable def cocycleIsKernel :
    IsLimit (KernelFork.ofι (cocycleInclusion X R n) (cocycle_wi X R n)) :=
  Fork.IsLimit.mk _ (fun s ↦ AddCommGrpCat.ofHom
    { toFun := fun x ↦
        ⟨((s.ι x : X ⟶ R.cocomplex.X n)), by
          have h : ((mappedCocomplex X R).sc n).g (s.ι x) = 0 :=
            _root_.CategoryTheory.ConcreteCategory.congr_hom s.condition x
          have hnext : (ComplexShape.up ℕ).next n = n + 1 :=
            ComplexShape.next_eq' _ (ComplexShape.up_mk _ _ rfl)
          have hg := sc_g_apply X R n (s.ι x)
          rw [hg] at h
          have h2 : ((s.ι x : X ⟶ R.cocomplex.X n) ≫
              R.cocomplex.d n ((ComplexShape.up ℕ).next n)) = 0 := h
          rw [hnext] at h2
          exact h2⟩
      map_zero' := by refine Subtype.ext ?_; exact map_zero _
      map_add' := fun _ _ => by refine Subtype.ext ?_; exact map_add _ _ _ })
    (by intro s; apply AddCommGrpCat.ext; intro x; rfl)
    (fun s l hl ↦ by
      apply AddCommGrpCat.ext
      intro x
      have h2 := _root_.CategoryTheory.ConcreteCategory.congr_hom hl x
      have h3 : ((l x).val : X ⟶ R.cocomplex.X n) =
          ((s.ι x : X ⟶ R.cocomplex.X n)) := h2
      exact Subtype.ext h3)

variable [HasInjectiveResolutions C] [HasExt.{v} C]

/-- Postcomposition with `Abelian.Ext.mk₀ g` as an additive map on `Ext` groups.
This is the covariant functoriality in the second argument used in the
naturality statement below. Alias of
`(_root_.CategoryTheory.Abelian.Ext.mk₀ g).postcomp X (add_zero n)`. -/
noncomputable abbrev extPostcompMk₀ {Y Y' : C} (g : Y ⟶ Y') (n : ℕ) :
    _root_.CategoryTheory.Abelian.Ext X Y n →+ _root_.CategoryTheory.Abelian.Ext X Y' n :=
  (_root_.CategoryTheory.Abelian.Ext.mk₀ g).postcomp X (add_zero n)

/-- The projection from cocycles to `Ext`, via the `extMk` cocycle calculus. -/
noncomputable def cocycleToExt :
    cocyclesObj X R n ⟶ AddCommGrpCat.of (_root_.CategoryTheory.Abelian.Ext X Y n) :=
  AddCommGrpCat.ofHom
    { toFun := fun c ↦ R.extMk c.val (n + 1) rfl c.property
      map_zero' := R.extMk_zero (n + 1) rfl
      map_add' := fun a b ↦
        (R.add_extMk a.val b.val (n + 1) rfl a.property b.property).symm }

/-- The map induced on cocycles by the chosen lift of `S.f` to cycles. -/
noncomputable def cyclesLiftMap :
    ((mappedCocomplex X R).sc n).X₁ ⟶ cocyclesObj X R n :=
  (cocycleIsKernel X R n).lift
    (KernelFork.ofι _ (((mappedCocomplex X R).sc n).zero))

omit [HasInjectiveResolutions C] [HasExt C] in
/-- The lift computes `S.f` on underlying morphisms. -/
lemma cyclesLiftMap_spec (t : ↥(((mappedCocomplex X R).sc n).X₁)) :
    (((cyclesLiftMap X R n ≫ cocycleInclusion X R n) t :
      X ⟶ R.cocomplex.X n)) =
      ((((mappedCocomplex X R).sc n).f t : X ⟶ R.cocomplex.X n)) := by
  have hfac : cyclesLiftMap X R n ≫ cocycleInclusion X R n =
      ((mappedCocomplex X R).sc n).f := by
    apply AddCommGrpCat.ext
    intro t
    rfl
  exact _root_.CategoryTheory.ConcreteCategory.congr_hom hfac t

omit [HasInjectiveResolutions C] in
/-- In degree zero, an `extMk` class vanishes only for the zero cocycle. -/
lemma extMk_zero_eq_zero {f : X ⟶ R.cocomplex.X 0}
    (hf : f ≫ R.cocomplex.d 0 1 = 0) (h0 : R.extMk f 1 rfl hf = 0) : f = 0 := by
  have h1 : R.extEquivCohomologyClass (R.extMk f 1 rfl hf) = 0 := by
    rw [h0]
    exact R.extEquivCohomologyClass_zero X 0
  rw [R.extEquivCohomologyClass_extMk] at h1
  rw [CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff] at h1
  rw [CochainComplex.HomComplex.Cocycle.fromSingleMk_mem_coboundaries_iff
    _ _ _ _ _ (-1) (by norm_num)] at h1
  obtain ⟨g, hg⟩ := h1
  have hX : IsZero (R.cochainComplex.X (-1)) :=
    CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by norm_num)
  have hg0 : g = 0 := IsZero.eq_of_tgt hX g 0
  rw [hg0, zero_comp] at hg
  have h2 : f = (f ≫ (R.cochainComplexXIso (0 : ℤ) 0 rfl).inv) ≫
      (R.cochainComplexXIso (0 : ℤ) 0 rfl).hom := by
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  -- `hg` mentions `(↑(0 : ℕ) : ℤ)` where `h2` has `(0 : ℤ)`; bridge by defeq.
  have hfi : (f ≫ (R.cochainComplexXIso (0 : ℤ) 0 rfl).inv) = 0 := hg.symm
  rw [hfi, zero_comp] at h2
  exact h2

omit [HasInjectiveResolutions C] in
/-- Boundaries map to zero in `Ext`: the cokernel condition for `π`.
Both cases go through explicitly typed pure-`C` intermediaries, so no rewrite
ever mentions a `prev`/`next` index inside a mapped-complex type. -/
lemma cocycle_wπ :
    cyclesLiftMap X R n ≫ cocycleToExt X R n = 0 := by
  apply AddCommGrpCat.ext
  intro t
  change (cocycleToExt X R n) ((cyclesLiftMap X R n) t) = 0
  have hval : (((cyclesLiftMap X R n) t).val : X ⟶ R.cocomplex.X n) =
      ((((mappedCocomplex X R).sc n).f t : X ⟶ R.cocomplex.X n)) :=
    cyclesLiftMap_spec X R n t
  cases n with
  | zero =>
    -- Degree zero: the incoming differential itself vanishes.
    have hd0 : R.cocomplex.d ((ComplexShape.up ℕ).prev 0) 0 = 0 :=
      R.cocomplex.shape _ _ (fun h => Nat.succ_ne_zero _ h)
    have hvan : (t : X ⟶ R.cocomplex.X ((ComplexShape.up ℕ).prev 0)) ≫
        R.cocomplex.d ((ComplexShape.up ℕ).prev 0) 0 = 0 := by
      rw [hd0]
      exact comp_zero
    have eSf : ((((mappedCocomplex X R).sc 0).f t : X ⟶ R.cocomplex.X 0)) = 0 :=
      hvan
    have e0 : ((((cyclesLiftMap X R 0) t).val : X ⟶ R.cocomplex.X 0)) = 0 :=
      hval.trans eSf
    have hz : (cyclesLiftMap X R 0) t = 0 := Subtype.ext e0
    rw [hz, map_zero]
  | succ k =>
    -- Positive degree: the image is a boundary by construction.
    have hprev : (ComplexShape.up ℕ).prev (k + 1) = k :=
      ComplexShape.prev_eq' _ (ComplexShape.up_mk _ _ rfl)
    have eSf : ((((mappedCocomplex X R).sc (k + 1)).f t :
        X ⟶ R.cocomplex.X (k + 1))) =
          (t : X ⟶ R.cocomplex.X ((ComplexShape.up ℕ).prev (k + 1))) ≫
          R.cocomplex.d ((ComplexShape.up ℕ).prev (k + 1)) (k + 1) :=
      sc_f_apply X R (k + 1) t
    have hmem : (t : X ⟶ R.cocomplex.X ((ComplexShape.up ℕ).prev (k + 1))) ≫
        R.cocomplex.d ((ComplexShape.up ℕ).prev (k + 1)) (k + 1)
        = (((cyclesLiftMap X R (k + 1)) t).val : X ⟶ R.cocomplex.X (k + 1)) :=
      eSf.symm.trans hval
    have hvan : R.extMk
        (((cyclesLiftMap X R (k + 1)) t).val : X ⟶ R.cocomplex.X (k + 1))
        (k + 2) rfl
        ((cyclesLiftMap X R (k + 1)) t).property = 0 := by
      have hiff := (R.extMk_eq_zero_iff _ (k + 2) rfl
        ((cyclesLiftMap X R (k + 1)) t).property
        ((ComplexShape.up ℕ).prev (k + 1)) (by rw [hprev])).mpr
      apply hiff
      exact ⟨_, hmem⟩
    exact hvan

omit [HasInjectiveResolutions C] in
/-- Two cocycles represent the same `Ext` class only if every cofork-coherent
map identifies them. -/
lemma cocycle_indep (s : CokernelCofork (cyclesLiftMap X R n))
    (c₁ c₂ : ↥(cocyclesObj X R n))
    (h : R.extMk c₁.val (n + 1) rfl c₁.property =
      R.extMk c₂.val (n + 1) rfl c₂.property) :
    s.π c₁ = s.π c₂ := by
  have hsubhf : (c₁.val - c₂.val) ≫ R.cocomplex.d n (n + 1) = 0 := by
    rw [_root_.CategoryTheory.Preadditive.sub_comp, c₁.property, c₂.property, sub_self]
  have hsub : R.extMk (c₁.val - c₂.val) (n + 1) rfl hsubhf = 0 := by
    have hsub2 := R.sub_extMk c₁.val c₂.val (n + 1) rfl
      c₁.property c₂.property
    rw [← hsub2, h, sub_self]
  have hcofork : cyclesLiftMap X R n ≫ s.π = 0 := s.condition
  cases n with
  | zero =>
    -- Degree zero: the difference cocycle itself vanishes.
    have hdiff : c₁.val - c₂.val = 0 :=
      extMk_zero_eq_zero X R _ hsub
    have hval : c₁.val = c₂.val := sub_eq_zero.mp hdiff
    have hce : c₁ = c₂ := Subtype.ext hval
    rw [hce]
  | succ k =>
    -- Positive degree: the difference is an explicit boundary. The witness
    -- `g` already lives over `prev (k + 1)`, so no transport is needed.
    have hprev : (ComplexShape.up ℕ).prev (k + 1) = k :=
      ComplexShape.prev_eq' _ (ComplexShape.up_mk _ _ rfl)
    obtain ⟨g, hg⟩ := (R.extMk_eq_zero_iff _ (k + 2) rfl _
      ((ComplexShape.up ℕ).prev (k + 1)) (by rw [hprev])).mp hsub
    have hgb : ((((mappedCocomplex X R).sc (k + 1)).f
        ((g : ↥(((mappedCocomplex X R).sc (k + 1)).X₁))) :
          X ⟶ R.cocomplex.X (k + 1))) =
        ((((g : ↥(((mappedCocomplex X R).sc (k + 1)).X₁))) :
          X ⟶ R.cocomplex.X ((ComplexShape.up ℕ).prev (k + 1))) ≫
          R.cocomplex.d ((ComplexShape.up ℕ).prev (k + 1)) (k + 1)) :=
      sc_f_apply X R (k + 1) _
    have hg2 : ((((g : ↥(((mappedCocomplex X R).sc (k + 1)).X₁))) :
          X ⟶ R.cocomplex.X ((ComplexShape.up ℕ).prev (k + 1))) ≫
          R.cocomplex.d ((ComplexShape.up ℕ).prev (k + 1)) (k + 1)) =
        c₁.val - c₂.val := hg
    have e1 : ((((cyclesLiftMap X R (k + 1))
        ((g : ↥(((mappedCocomplex X R).sc (k + 1)).X₁)))).val :
        X ⟶ R.cocomplex.X (k + 1))) = c₁.val - c₂.val :=
      (cyclesLiftMap_spec X R (k + 1) _).trans (hgb.trans hg2)
    have hcb2 : cyclesLiftMap X R (k + 1)
        ((g : ↥(((mappedCocomplex X R).sc (k + 1)).X₁))) = c₁ - c₂ :=
      Subtype.ext e1
    have hfin : s.π (c₁ - c₂) = 0 := by
      rw [← hcb2]
      have h5 := _root_.CategoryTheory.ConcreteCategory.congr_hom hcofork
        ((g : ↥(((mappedCocomplex X R).sc (k + 1)).X₁)))
      exact h5
    have hsub2 : s.π c₁ - s.π c₂ = 0 := by
      rw [← map_sub]
      exact hfin
    exact sub_eq_zero.mp hsub2

/-- `Ext` with the `extMk` projection is the cokernel of the incoming map:
the universal property, proved by choosing cocycle representatives. -/
noncomputable def cocycleCokernelIsColimit :
    IsColimit (CokernelCofork.ofπ (cocycleToExt X R n) (cocycle_wπ X R n)) := by
  have rep : ∀ e : _root_.CategoryTheory.Abelian.Ext X Y n, ∃ c : ↥(cocyclesObj X R n),
      R.extMk c.val (n + 1) rfl c.property = e := by
    intro e
    obtain ⟨f, hf, hfe⟩ := R.extMk_surjective e (n + 1) rfl
    exact ⟨⟨f, hf⟩, hfe⟩
  classical
  refine Cofork.IsColimit.mk _ (fun s ↦ AddCommGrpCat.ofHom
    { toFun := fun e ↦ s.π (Classical.choose (rep e))
      map_zero' := ?_
      map_add' := ?_ }) ?_ ?_
  · -- The chosen representative of `0` differs from `0` by a boundary.
    have h0 : R.extMk (Classical.choose (rep 0)).val (n + 1) rfl
        (Classical.choose (rep 0)).property = 0 :=
      Classical.choose_spec (rep 0)
    have h0' : R.extMk (Classical.choose (rep 0)).val (n + 1) rfl
        (Classical.choose (rep 0)).property =
        R.extMk (0 : ↥(cocyclesObj X R n)).val (n + 1) rfl
          (0 : ↥(cocyclesObj X R n)).property :=
      h0.trans (R.extMk_zero (n + 1) rfl).symm
    have hindep0 := cocycle_indep X R n s (Classical.choose (rep 0)) 0 h0'
    simpa using hindep0
  · intro e₁ e₂
    have eA : R.extMk (Classical.choose (rep (e₁ + e₂))).val (n + 1) rfl
        (Classical.choose (rep (e₁ + e₂))).property = e₁ + e₂ :=
      Classical.choose_spec (rep (e₁ + e₂))
    have eB : e₁ + e₂ = R.extMk (Classical.choose (rep e₁)).val (n + 1) rfl
          (Classical.choose (rep e₁)).property +
        R.extMk (Classical.choose (rep e₂)).val (n + 1) rfl
          (Classical.choose (rep e₂)).property := by
      rw [Classical.choose_spec (rep e₁), Classical.choose_spec (rep e₂)]
    have eC : R.extMk (Classical.choose (rep e₁)).val (n + 1) rfl
          (Classical.choose (rep e₁)).property +
        R.extMk (Classical.choose (rep e₂)).val (n + 1) rfl
          (Classical.choose (rep e₂)).property =
        R.extMk ((Classical.choose (rep e₁)).val +
          (Classical.choose (rep e₂)).val) (n + 1) rfl _ :=
      R.add_extMk _ _ (n + 1) rfl _ _
    have eD : R.extMk ((Classical.choose (rep e₁)).val +
          (Classical.choose (rep e₂)).val) (n + 1) rfl _ =
        R.extMk ((Classical.choose (rep e₁) + Classical.choose (rep e₂))).val
          (n + 1) rfl
          (Classical.choose (rep e₁) + Classical.choose (rep e₂)).property :=
      rfl
    have hsum : R.extMk (Classical.choose (rep (e₁ + e₂))).val (n + 1) rfl
        (Classical.choose (rep (e₁ + e₂))).property =
        R.extMk ((Classical.choose (rep e₁) + Classical.choose (rep e₂))).val
          (n + 1) rfl
          (Classical.choose (rep e₁) + Classical.choose (rep e₂)).property :=
      eA.trans (eB.trans (eC.trans eD))
    have hindep := cocycle_indep X R n s (Classical.choose (rep (e₁ + e₂)))
      (Classical.choose (rep e₁) + Classical.choose (rep e₂)) hsum
    have hmap : s.π (Classical.choose (rep e₁) + Classical.choose (rep e₂)) =
        s.π (Classical.choose (rep e₁)) + s.π (Classical.choose (rep e₂)) :=
      map_add _ _ _
    rw [hmap] at hindep
    exact hindep
  · intro s
    apply AddCommGrpCat.ext
    intro c
    change s.π (Classical.choose (rep ((cocycleToExt X R n) c))) = s.π c
    have hc : R.extMk (Classical.choose
        (rep ((cocycleToExt X R n) c))).val (n + 1) rfl
        (Classical.choose (rep ((cocycleToExt X R n) c))).property =
        R.extMk c.val (n + 1) rfl c.property := by
      rw [Classical.choose_spec (rep ((cocycleToExt X R n) c))]
      rfl
    exact cocycle_indep X R n s _ _ hc
  · intro s m hm
    apply AddCommGrpCat.ext
    intro e
    change m e = s.π (Classical.choose (rep e))
    have he : e = R.extMk (Classical.choose (rep e)).val (n + 1) rfl
        (Classical.choose (rep e)).property :=
      (Classical.choose_spec (rep e)).symm
    have hm2 : ((cocycleToExt X R n) ≫ m) (Classical.choose (rep e)) =
        s.π (Classical.choose (rep e)) := _root_.CategoryTheory.ConcreteCategory.congr_hom hm _
    have happ : ((cocycleToExt X R n) ≫ m) (Classical.choose (rep e)) =
        m (R.extMk (Classical.choose (rep e)).val (n + 1) rfl
          (Classical.choose (rep e)).property) := rfl
    rw [happ, ← he] at hm2
    exact hm2

/-- Left homology data exhibiting `Ext` as the homology of the mapped complex
at degree `n`. An `abbrev` so that projections such as `.K` unfold reducibly
and rewrite motives over short-complex morphisms stay type-correct. -/
noncomputable abbrev homologyDataExt :
    ((mappedCocomplex X R).sc n).LeftHomologyData where
  K := cocyclesObj X R n
  H := AddCommGrpCat.of (_root_.CategoryTheory.Abelian.Ext X Y n)
  i := cocycleInclusion X R n
  π := cocycleToExt X R n
  wi := cocycle_wi X R n
  hi := cocycleIsKernel X R n
  wπ := cocycle_wπ X R n
  hπ := cocycleCokernelIsColimit X R n

/-- An isomorphism in `AddCommGrpCat` induces an additive equivalence of the
underlying groups. Alias of `_root_.CategoryTheory.Iso.addCommGroupIsoToAddEquiv`. -/
noncomputable abbrev isoToAddEquiv {M N : AddCommGrpCat.{v}} (e : M ≅ N) :
    ↥M ≃+ ↥N :=
  e.addCommGroupIsoToAddEquiv

/-- The right-derived functors of `preadditiveCoyoneda.obj (op X)` compute
`Abelian.Ext X _`, as an additive equivalence on underlying groups. -/
noncomputable def rightDerivedCoyonedaObjAddEquiv :
    ↥(((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n).obj Y) ≃+
      _root_.CategoryTheory.Abelian.Ext X Y n :=
  isoToAddEquiv ((R.isoRightDerivedObj
    (preadditiveCoyoneda.obj (Opposite.op X)) n).trans
    (homologyDataExt X R n).homologyIso)

/-- The induced map on cocycles for naturality: postcomposition with a lift
between injective resolutions. The goal is first exposed as a pure-`C`
equation via `show`, so the commutation rewrite never touches subgroup
membership. -/
noncomputable def gammaCyclesMap {Y' : C} (R' : InjectiveResolution Y')
    {g : Y ⟶ Y'} (φ : _root_.CategoryTheory.InjectiveResolution.Hom R R' g) :
    cocyclesObj X R n ⟶ cocyclesObj X R' n :=
  AddCommGrpCat.ofHom
    { toFun := fun c ↦
        ⟨((c.val ≫ φ.hom.f n : X ⟶ R'.cocomplex.X n)), by
          have hc : c.val ≫ R.cocomplex.d n (n + 1) = 0 := c.property
          have hcomm := φ.hom.comm' n (n + 1)
            (ComplexShape.up_mk _ _ rfl)
          change (c.val ≫ φ.hom.f n) ≫ R'.cocomplex.d n (n + 1) = 0
          calc (c.val ≫ φ.hom.f n) ≫ R'.cocomplex.d n (n + 1)
              = c.val ≫ (φ.hom.f n ≫ R'.cocomplex.d n (n + 1)) := by
                rw [Category.assoc]
            _ = c.val ≫ (R.cocomplex.d n (n + 1) ≫ φ.hom.f (n + 1)) := by
                rw [hcomm]
            _ = (c.val ≫ R.cocomplex.d n (n + 1)) ≫ φ.hom.f (n + 1) := by
                rw [← Category.assoc]
            _ = 0 := by rw [hc, zero_comp]⟩
      map_zero' := by
        refine Subtype.ext ?_
        simp
      map_add' := fun _ _ => by
        refine Subtype.ext ?_
        simp [Preadditive.add_comp] }

omit [HasInjectiveResolutions C] [HasExt C] in
/-- The induced map on cocycles commutes with the inclusions. -/
lemma gammaCyclesMap_commi {Y' : C} (R' : InjectiveResolution Y')
    {g : Y ⟶ Y'} (φ : _root_.CategoryTheory.InjectiveResolution.Hom R R' g) :
    gammaCyclesMap X R n R' φ ≫ cocycleInclusion X R' n =
      cocycleInclusion X R n ≫
        ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{v}
          (ComplexShape.up ℕ) n).map
          (((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex
            (ComplexShape.up ℕ)).map φ.hom)).τ₂ := by
  apply AddCommGrpCat.ext
  intro c
  rfl

/-- The map data witnessing naturality on cycles and on `Ext`. -/
noncomputable def gammaMapData {Y' : C} (R' : InjectiveResolution Y')
    {g : Y ⟶ Y'} (φ : _root_.CategoryTheory.InjectiveResolution.Hom R R' g) :
    _root_.CategoryTheory.ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{v}
        (ComplexShape.up ℕ) n).map
        (((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex
          (ComplexShape.up ℕ)).map φ.hom))
      (homologyDataExt X R n) (homologyDataExt X R' n) where
  φK := gammaCyclesMap X R n R' φ
  φH := AddCommGrpCat.ofHom (extPostcompMk₀ X g n)
  commi := gammaCyclesMap_commi X R n R' φ
  -- Entirely term-style (`Category.assoc` and `congrArg` with explicit
  -- lambdas, checked by `exact` at default transparency): no `rw`/`simp`
  -- motive is ever built over the `K`-vs-`cocyclesObj` unfolding gap.
  commf' := by
    have hf1 : (homologyDataExt X R n).f' ≫ (homologyDataExt X R n).i =
        ((mappedCocomplex X R).sc n).f :=
      _root_.CategoryTheory.ShortComplex.LeftHomologyData.f'_i _
    have hf2 : (homologyDataExt X R' n).f' ≫ (homologyDataExt X R' n).i =
        ((mappedCocomplex X R').sc n).f :=
      _root_.CategoryTheory.ShortComplex.LeftHomologyData.f'_i _
    have hcommi : gammaCyclesMap X R n R' φ ≫ (homologyDataExt X R' n).i =
        (homologyDataExt X R n).i ≫
          ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{v}
            (ComplexShape.up ℕ) n).map
            (((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex
              (ComplexShape.up ℕ)).map φ.hom)).τ₂ :=
      gammaCyclesMap_commi X R n R' φ
    have hMono : Mono (homologyDataExt X R' n).i :=
      ⟨fun _ _ => Fork.IsLimit.hom_ext (cocycleIsKernel X R' n)⟩
    have epost : ((homologyDataExt X R n).f' ≫ gammaCyclesMap X R n R' φ) ≫
        (homologyDataExt X R' n).i =
        ((((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{v}
          (ComplexShape.up ℕ) n).map
          (((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex
            (ComplexShape.up ℕ)).map φ.hom)).τ₁ ≫
          (homologyDataExt X R' n).f') ≫ (homologyDataExt X R' n).i) :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun x => (homologyDataExt X R n).f' ≫ x) hcommi).trans
          (((Category.assoc _ _ _).symm.trans
            ((congrArg (fun x => x ≫ _) hf1).trans
              ((ShortComplex.Hom.comm₁₂ _).symm.trans
                ((congrArg (fun x => _ ≫ x) hf2.symm).trans
                  (Category.assoc _ _ _).symm))))))
    exact hMono.right_cancellation _ _ epost
  commπ := by
    apply AddCommGrpCat.ext
    intro c
    exact R.extMk_comp_mk₀ c.val (n + 1) rfl c.property φ

/-- The comparison is natural in `Y`: pushing a class forward along
`g : Y ⟶ Y'` corresponds to postcomposition with `Ext.mk₀ g`. -/
theorem rightDerivedCoyonedaObjAddEquiv_naturality {Y' : C}
    (R' : InjectiveResolution Y') {g : Y ⟶ Y'}
    (φ : _root_.CategoryTheory.InjectiveResolution.Hom R R' g)
    (a : ↥(((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n).obj Y)) :
    (rightDerivedCoyonedaObjAddEquiv X R' n)
      (((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n).map g a) =
      ((rightDerivedCoyonedaObjAddEquiv X R n) a).comp
        (_root_.CategoryTheory.Abelian.Ext.mk₀ g) (add_zero n) := by
  classical
  let F := preadditiveCoyoneda.obj (Opposite.op X)
  let ψ := (F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom
  let scMap := (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{v}
    (ComplexShape.up ℕ) n).map ψ
  have hmap := _root_.CategoryTheory.Functor.rightDerived_map_eq F n g φ.hom φ.ι_comp_hom
  have hcomm :=
    _root_.CategoryTheory.ShortComplex.LeftHomologyMapData.homologyMap_comm scMap
      (gammaMapData X R n R' φ)
  have hmap2 : ((F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{v}
          (ComplexShape.up ℕ) n).map φ.hom) =
        _root_.CategoryTheory.ShortComplex.homologyMap scMap := rfl
  -- Term-style throughout (`Category.assoc` and `congrArg` with explicit
  -- lambdas): no `rw`/`simp` motive is ever built over the
  -- `homologyMap`/`homologyIso` domain mismatch.
  have key' : (R'.isoRightDerivedObj F n).inv ≫
      ((R'.isoRightDerivedObj F n).hom ≫
        (homologyDataExt X R' n).homologyIso.hom) =
      (homologyDataExt X R' n).homologyIso.hom :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun x => x ≫ (homologyDataExt X R' n).homologyIso.hom)
        (Iso.inv_hom_id _)).trans (Category.id_comp _))
  have hφH : (gammaMapData X R n R' φ).φH =
      AddCommGrpCat.ofHom (extPostcompMk₀ X g n) := rfl
  have hmor : (F.rightDerived n).map g ≫
      ((R'.isoRightDerivedObj F n).trans
        (homologyDataExt X R' n).homologyIso).hom =
      ((R.isoRightDerivedObj F n).trans
        (homologyDataExt X R n).homologyIso).hom ≫
      AddCommGrpCat.ofHom (extPostcompMk₀ X g n) := by
    rw [hmap, hmap2]
    change (((R.isoRightDerivedObj F n).hom ≫ _root_.CategoryTheory.ShortComplex.homologyMap scMap ≫
        (R'.isoRightDerivedObj F n).inv) ≫
        ((R'.isoRightDerivedObj F n).hom ≫
          (homologyDataExt X R' n).homologyIso.hom)) =
      (((R.isoRightDerivedObj F n).hom ≫
        (homologyDataExt X R n).homologyIso.hom) ≫
        AddCommGrpCat.ofHom (extPostcompMk₀ X g n))
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun x => ((R.isoRightDerivedObj F n).hom ≫
        _root_.CategoryTheory.ShortComplex.homologyMap scMap) ≫ x) key').trans
        (((Category.assoc _ _ _).trans
          (congrArg (fun x => (R.isoRightDerivedObj F n).hom ≫ x)
            hcomm)).trans
          (((congrArg (fun x => (R.isoRightDerivedObj F n).hom ≫ x)
            (congrArg (fun x => (homologyDataExt X R n).homologyIso.hom ≫ x)
              hφH)).trans
            (Category.assoc _ _ _).symm))))
  have happ := _root_.CategoryTheory.ConcreteCategory.congr_hom hmor a
  exact happ

end CategoryTheory.DerivedCoyoneda

namespace CategoryTheory.Abelian

variable [HasInjectiveResolutions C] [HasExt.{v} C]

/-- The right-derived functors of `preadditiveCoyoneda.obj (Opposite.op X)`
are naturally isomorphic to the canonical covariant Ext functors
`extFunctorObj X n`. -/
noncomputable def rightDerivedCoyonedaIsoExtFunctorObj (X : C) (n : ℕ) :
    (preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n ≅
      extFunctorObj X n :=
  NatIso.ofComponents
    (fun Y => AddEquiv.toAddCommGrpIso
      (DerivedCoyoneda.rightDerivedCoyonedaObjAddEquiv X
        (injectiveResolution Y) n))
    (fun {Y Y'} g => by
      apply AddCommGrpCat.hom_ext
      ext a
      let φ := InjectiveResolution.descHom g
        (injectiveResolution Y) (injectiveResolution Y')
      exact DerivedCoyoneda.rightDerivedCoyonedaObjAddEquiv_naturality
        X (injectiveResolution Y) n (injectiveResolution Y') φ a)

end CategoryTheory.Abelian

end


/-
Authors of the representative calculation: @toskua and Avocado.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.DerivedCoyoneda

namespace CategoryTheory.Abelian
universe v₀ u₀
variable {C : Type u₀} [Category.{v₀} C] [Abelian C]
  [HasInjectiveResolutions C] [HasExt.{v₀} C]

/-- The inverse functor-level Coyoneda comparison sends every injective-resolution
representative to its canonical homology class. -/
theorem rightDerivedCoyonedaIsoExtFunctorObj_inv_extMk (Z Y : C) (q : ℕ)
    (f : Z ⟶ (injectiveResolution Y).cocomplex.X q)
    (hf : f ≫ (injectiveResolution Y).cocomplex.d q (q + 1) = 0) :
    let R := injectiveResolution Y
    let hE := homologyDataExt Z R q
    let c : hE.K := ⟨f, hf⟩
    ((Abelian.rightDerivedCoyonedaIsoExtFunctorObj Z q).app Y).inv
        (R.extMk f (q + 1) rfl hf) =
      (R.isoRightDerivedObj (preadditiveCoyoneda.obj (op Z)) q).inv
        (((mappedCocomplex Z R).sc q).homologyπ (hE.cyclesIso.inv c)) := by
  let R := injectiveResolution Y
  let hE := homologyDataExt Z R q
  let c : hE.K := ⟨f, hf⟩
  have hπ : hE.homologyIso.inv (R.extMk f (q + 1) rfl hf) =
      ((mappedCocomplex Z R).sc q).homologyπ (hE.cyclesIso.inv c) :=
    ConcreteCategory.congr_hom hE.π_comp_homologyIso_inv c
  change (R.isoRightDerivedObj (preadditiveCoyoneda.obj (op Z)) q).inv
    (hE.homologyIso.inv _) = _
  exact congrArg (R.isoRightDerivedObj (preadditiveCoyoneda.obj (op Z)) q).inv hπ

end CategoryTheory.Abelian

end
