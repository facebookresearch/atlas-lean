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
# Right-derived Coyoneda and resolution Ext classes

Let `C` be abelian with injective resolutions and Ext in its hom-set
universe `v`. For `X,Y : C`, applying `Hom_C(X,-)` to an injective
resolution of `Y` gives the cocycles `f : X → I^n` with
`f ≫ d_I=0`. Their quotient by incoming boundaries is `Ext^n(X,Y)`.
This gives an additive equivalence and a natural functor isomorphism
`R^nHom_C(X,-) ≅ Ext^n(X,-)`, with coefficient maps given by
postcomposition with degree-zero Ext classes. The object universe of
`C` is independent of `v`.
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

/- This abbreviation is reducible so index rewrites do not require semireducible unfolding in mapped-complex motives. -/

/-- Let `C` be abelian with hom-set universe `v`, `X : C`, and
`I` an injective resolution of `Y`. Applying additive Coyoneda gives the nonnegative cochain
complex with degree-`n` group `Hom_C(X,I^n)` in `Ab_v` and
differentials given by postcomposition with those of `I`. -/
noncomputable abbrev mappedCocomplex : CochainComplex AddCommGrpCat.{v} ℕ :=
  ((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex _).obj
    R.cocomplex

/-- Let `C` be abelian with hom-set universe `v`, `X : C`, and
`I` an injective resolution of `Y`. The degree-`n` cocycle subgroup consists of maps
`f : X → I^n` satisfying `f ≫ d_I^n=0`, with its inherited
additive group structure. -/
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

/-- Let `C` be abelian with hom-set universe `v`, `X : C`, and
`I` an injective resolution of `Y`. The degree-`n` cocycle subgroup of `Hom_C(X,I^n)` defines
an additive-group object of `Ab_v`. -/
def cocyclesObj : AddCommGrpCat.{v} :=
  AddCommGrpCat.of (cocycleSubgroup X R n)

/- The type ascriptions are kept transparent for index rewriting. -/

/-- Let `C` be abelian with hom-set universe `v`, `X : C`, and
`I` an injective resolution of `Y`. The outgoing differential in degree `n` of the mapped
Coyoneda short complex takes `f : X → I^n` to
`f ≫ d_I(n,next(n))`. -/
lemma sc_g_apply (y : ↥(((mappedCocomplex X R).sc n).X₂)) :
    ((mappedCocomplex X R).sc n).g y =
      (((y : X ⟶ R.cocomplex.X n) ≫
        R.cocomplex.d n ((ComplexShape.up ℕ).next n) :
        X ⟶ R.cocomplex.X ((ComplexShape.up ℕ).next n)) :
        ↥(((mappedCocomplex X R).sc n).X₃)) := rfl

/-- Let `C` be abelian with hom-set universe `v`, `X : C`, and
`I` an injective resolution of `Y`. The incoming differential of the mapped degree-`n` short
complex is postcomposition with `d_I(prev(n),n)`. In degree zero,
this map is zero because the nonnegative cochain shape has no
incoming differential. -/
lemma sc_f_apply (t : ↥(((mappedCocomplex X R).sc n).X₁)) :
    ((mappedCocomplex X R).sc n).f t =
      (((t : X ⟶ R.cocomplex.X ((ComplexShape.up ℕ).prev n)) ≫
        R.cocomplex.d ((ComplexShape.up ℕ).prev n) n :
        X ⟶ R.cocomplex.X n) :
        ↥(((mappedCocomplex X R).sc n).X₂)) := rfl

/-- Let `C` be abelian with hom-set universe `v`, `X : C`, and
`I` an injective resolution of `Y`. The cocycle inclusion sends the degree-`n` subgroup into
`Hom_C(X,I^n)` by its underlying morphism. -/
def cocycleInclusion :
    cocyclesObj X R n ⟶ ((mappedCocomplex X R).sc n).X₂ :=
  AddCommGrpCat.ofHom
    { toFun := fun c ↦ ((c.val : X ⟶ R.cocomplex.X n) :
        ↥(((mappedCocomplex X R).sc n).X₂))
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/- The proof rewrites the index equality in C before using the mapped short-complex type. -/

/-- Let `C` be abelian with hom-set universe `v`, `X : C`, and
`I` an injective resolution of `Y`. The cocycle inclusion followed by the outgoing Hom-complex
differential is zero. -/
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

/- The kernel proof uses a C-valued intermediary for the index equality. -/

/-- Let `C` be abelian with hom-set universe `v`, `X : C`, and
`I` an injective resolution of `Y`. The degree-`n` cocycle inclusion is a kernel of the outgoing
postcomposition differential `Hom_C(X,I^n) → Hom_C(X,I^(n+1))`. -/
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

/-- Let `C` be abelian with hom-set universe `v`, injective
resolutions, and Ext in universe `v`. Let `X : C` and `I` be an
injective resolution of `Y`. For `g : Y → Y′`, Ext postcomposition by its degree-zero
class is the additive map `Ext^n(X,Y) → Ext^n(X,Y′)`. -/
noncomputable abbrev extPostcompMk₀ {Y Y' : C} (g : Y ⟶ Y') (n : ℕ) :
    _root_.CategoryTheory.Abelian.Ext X Y n →+ _root_.CategoryTheory.Abelian.Ext X Y' n :=
  (_root_.CategoryTheory.Abelian.Ext.mk₀ g).postcomp X (add_zero n)

/-- Let `C` be abelian with hom-set universe `v`, injective
resolutions, and Ext in universe `v`. Let `X : C` and `I` be an
injective resolution of `Y`. The projection from degree-`n` cocycles to `Ext^n(X,Y)`
sends `f : X → I^n` to the canonical Ext class represented by that
resolution cocycle. -/
noncomputable def cocycleToExt :
    cocyclesObj X R n ⟶ AddCommGrpCat.of (_root_.CategoryTheory.Abelian.Ext X Y n) :=
  AddCommGrpCat.ofHom
    { toFun := fun c ↦ R.extMk c.val (n + 1) rfl c.property
      map_zero' := R.extMk_zero (n + 1) rfl
      map_add' := fun a b ↦
        (R.add_extMk a.val b.val (n + 1) rfl a.property b.property).symm }

/-- Let `C` be abelian with hom-set universe `v`, injective
resolutions, and Ext in universe `v`. Let `X : C` and `I` be an
injective resolution of `Y`. The incoming Hom-complex differential factors through the
cocycle subgroup, giving the boundary map from its preceding term
to the degree-`n` cocycles. -/
noncomputable def cyclesLiftMap :
    ((mappedCocomplex X R).sc n).X₁ ⟶ cocyclesObj X R n :=
  (cocycleIsKernel X R n).lift
    (KernelFork.ofι _ (((mappedCocomplex X R).sc n).zero))

omit [HasInjectiveResolutions C] [HasExt C] in
/-- Let `C` be abelian with hom-set universe `v`, injective
resolutions, and Ext in universe `v`. Let `X : C` and `I` be an
injective resolution of `Y`. The incoming boundary map followed by the cocycle inclusion
is the incoming differential of the degree-`n` Hom short complex. -/
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
/-- Let `C` be abelian with hom-set universe `v`, injective
resolutions, and Ext in universe `v`. Let `X : C` and `I` be an
injective resolution of `Y`. If a degree-zero cocycle `f : X → I⁰` represents the zero
class in `Ext⁰(X,Y)`, then `f=0`. -/
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
/- The proof handles predecessor and successor indices in explicitly typed C-valued intermediaries. -/

/-- Let `C` be abelian with hom-set universe `v`, injective
resolutions, and Ext in universe `v`. Let `X : C` and `I` be an
injective resolution of `Y`. Every incoming boundary maps to zero under the cocycle
projection to `Ext^n(X,Y)`. -/
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
/-- Let `C` be abelian with hom-set universe `v`, injective
resolutions, and Ext in universe `v`. Let `X : C` and `I` be an
injective resolution of `Y`. If two degree-`n` cocycles represent the same Ext class,
any additive-group map from cocycles annihilating incoming boundaries
takes them to the same value. -/
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

/-- Let `C` be abelian with hom-set universe `v`, injective
resolutions, and Ext in universe `v`. Let `X : C` and `I` be an
injective resolution of `Y`. The cocycle projection to `Ext^n(X,Y)` exhibits that group
as the cokernel of the incoming boundary map into the cocycles. -/
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

/- The abbreviation keeps its projections reducible for short-complex rewrite motives. -/

/-- Let `C` be abelian with hom-set universe `v`, injective
resolutions, and Ext in universe `v`. Let `X : C` and `I` be an
injective resolution of `Y`. The cocycle kernel and its quotient to `Ext^n(X,Y)` give
left-homology data for the degree-`n` short complex of `Hom_C(X,I)`:
its homology object is the Ext group. -/
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

/-- An isomorphism `M ≅ N` of additive-group objects in `Ab_v`
gives an additive equivalence of the underlying groups, with forward
and inverse maps those of the isomorphism. -/
noncomputable abbrev isoToAddEquiv {M N : AddCommGrpCat.{v}} (e : M ≅ N) :
    ↥M ≃+ ↥N :=
  e.addCommGroupIsoToAddEquiv

/-- Let `C` be abelian with hom-set universe `v`, injective
resolutions, and Ext in universe `v`. Let `X : C` and `I` be an
injective resolution of `Y`. The chosen resolution comparisons and its Ext homology
presentation give an additive equivalence
`R^nHom_C(X,-)(Y) ≃+ Ext^n(X,Y)`. -/
noncomputable def rightDerivedCoyonedaObjAddEquiv :
    ↥(((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n).obj Y) ≃+
      _root_.CategoryTheory.Abelian.Ext X Y n :=
  isoToAddEquiv ((R.isoRightDerivedObj
    (preadditiveCoyoneda.obj (Opposite.op X)) n).trans
    (homologyDataExt X R n).homologyIso)

/- The cochain compatibility equation is exposed in C before rewriting subgroup membership. -/

/-- Let `C` be abelian with hom-set universe `v`, injective
resolutions, and Ext in universe `v`. Let `X : C` and `I` be an
injective resolution of `Y`. For an injective resolution `I′` of `Y′` and a lift
`φ : I → I′` of `g : Y → Y′`, the map on degree-`n` cocycles
is postcomposition `f ↦ f ≫ φ^n`. -/
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
/-- Let `C` be abelian with hom-set universe `v`, injective
resolutions, and Ext in universe `v`. Let `X : C` and `I` be an
injective resolution of `Y`. For a resolution lift `φ : I → I′` over `g : Y → Y′`,
postcomposition on cocycles commutes with their inclusions into
`Hom_C(X,I^n)` and `Hom_C(X,I′^n)`. -/
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

/-- Let `C` be abelian with hom-set universe `v`, injective
resolutions, and Ext in universe `v`. Let `X : C` and `I` be an
injective resolution of `Y`. A resolution lift `φ : I → I′` over `g : Y → Y′` gives
left-homology map data: its cycle map is postcomposition by `φ^n`,
and its Ext map is postcomposition by the degree-zero class of `g`. -/
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

/-- Let `C` be abelian with hom-set universe `v`, injective
resolutions, and Ext in universe `v`. Let `X : C` and `I` be an
injective resolution of `Y`. For a resolution lift over `g : Y → Y′`, the additive
comparisons intertwine the derived coefficient map with
`a ↦ a.comp(Ext.mk₀(g))` on `Ext^n(X,Y)`. -/
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

/-- Let `C` be abelian with hom-set universe `v`, injective
resolutions, and Ext in universe `v`. For fixed `X : C`, the
resolution comparisons give a natural isomorphism of additive-group
functors `R^nHom_C(X,-) ≅ Ext^n(X,-)`. -/
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

/-- Let `C` be abelian with hom-set universe `v`, injective
resolutions, and Ext in universe `v`. For the chosen injective
resolution `I` of `Y`, a cocycle `f : Z → I^q` gives an Ext class.
The inverse canonical Coyoneda-to-Ext comparison sends it to its
Hom-complex cohomology class, transported to `R^qHom_C(Z,-)(Y)`
by the inverse resolution comparison. -/
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
