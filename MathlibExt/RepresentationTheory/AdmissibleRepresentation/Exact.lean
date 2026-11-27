/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RepresentationTheory.AdmissibleRepresentation.Regular
public import Mathlib.RingTheory.Flat.Basic

/-!
# Admissible representations: subobjects, quotients, direct sums, exactness, faithfulness

Let `F` be a field, `G` a group acting on a commutative `F`-algebra `S`, `H` a subgroup of `G`
and `E = S^H`. The functor `D_S(V) = (S ⊗_F V)^H` on representations of `G`
(`Representation.periods`, `Representation.periodsMap`) is left exact for every `S`: it preserves
injective intertwining maps (`Representation.periodsMap_injective`) and exactness at the middle of
a sequence `0 → V₁ → V₂ → V₃` (`Representation.exact_periodsMap_of_injective`), since `S` is flat
over `F` and taking invariants is left exact.

For an `(F, H)`-regular ring `S` (`Representation.IsRegularPeriodRing`), dimension counting with
`dim_E D_S(V) ≤ dim_F V` gives the first part of Fontaine–Ouyang, Theorem 3.14 (2), and of
J.-M. Fontaine, *Représentations p-adiques semi-stables*, Astérisque 223 (1994), Exposé III,
Proposition 1.5.2 p. 124 (proof in §1.5.3 p. 124): admissible representations are closed under

* subobjects and quotients: for a short exact sequence `0 → V₁ → V₂ → V₃ → 0` with `V₂`
  admissible, `V₁` and `V₃` are admissible
  (`Representation.IsRegularPeriodRing.isAdmissible_of_exact`), in particular every
  subrepresentation and every quotient of an admissible representation is admissible
  (`Representation.IsRegularPeriodRing.isAdmissible_toRepresentation`,
  `Representation.IsRegularPeriodRing.isAdmissible_quotient`);
* direct sums: `V₁ × V₂` is admissible if and only if `V₁` and `V₂` are
  (`Representation.IsRegularPeriodRing.isAdmissible_prod_iff`), as
  `D_S(V₁ × V₂) ≃ D_S(V₁) × D_S(V₂)` (`Representation.periodsProdEquiv`);

and on admissible representations `D_S` is

* exact: it maps a short exact sequence with admissible middle term to a short exact sequence
  (`Representation.IsRegularPeriodRing.shortExact_periodsMap`), and more generally an exact
  sequence `V₁ → V₂ → V₃` with `V₁` admissible to an exact sequence
  (`Representation.IsRegularPeriodRing.exact_periodsMap`);
* faithful: intertwining maps `f, f'` out of an admissible representation with
  `D_S(f) = D_S(f')` are equal (`Representation.IsRegularPeriodRing.eq_of_periodsMap_eq`), as
  `α_V` is onto.

The inclusion of a subrepresentation and the projection onto the quotient are recorded as
intertwining maps (`Subrepresentation.subtype`, `Subrepresentation.mkQ`). Only abstract group
actions occur: no topology is involved and continuity is never assumed.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Subrepresentation

section Subtype

variable {A G W : Type*} [Semiring A] [Monoid G] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G W}

/-- **The inclusion of a subrepresentation** `W'` of `ρ`, as an intertwining map from
`W'.toRepresentation` to `ρ`. -/
def subtype (W' : Subrepresentation ρ) : W'.toRepresentation.IntertwiningMap ρ where
  toLinearMap := W'.toSubmodule.subtype
  isIntertwining' _ := LinearMap.ext fun _ => rfl

/-- The inclusion of a subrepresentation maps `w` to `w`. -/
@[simp]
theorem subtype_apply (W' : Subrepresentation ρ) (w : W'.toSubmodule) : W'.subtype w = w :=
  rfl

/-- The inclusion of a subrepresentation is injective. -/
theorem subtype_injective (W' : Subrepresentation ρ) : Function.Injective W'.subtype :=
  Subtype.val_injective

end Subtype

section Quotient

variable {A G W : Type*} [Ring A] [Monoid G] [AddCommGroup W] [Module A W]
  {ρ : Representation A G W}

/-- **The projection onto the quotient by a subrepresentation** `W'` of `ρ`, as an intertwining
map from `ρ` to `W'.quotient`. -/
def mkQ (W' : Subrepresentation ρ) : ρ.IntertwiningMap W'.quotient where
  toLinearMap := W'.toSubmodule.mkQ
  isIntertwining' _ := LinearMap.ext fun _ => rfl

/-- The projection onto the quotient maps `w` to its class. -/
@[simp]
theorem mkQ_apply (W' : Subrepresentation ρ) (w : W) :
    W'.mkQ w = Submodule.Quotient.mk (p := W'.toSubmodule) w :=
  rfl

/-- The projection onto the quotient by a subrepresentation is surjective. -/
theorem mkQ_surjective (W' : Subrepresentation ρ) : Function.Surjective W'.mkQ :=
  Submodule.mkQ_surjective _

/-- `0 → W' → W → W ⧸ W' → 0` is exact at `W`. -/
theorem exact_subtype_mkQ (W' : Subrepresentation ρ) : Function.Exact W'.subtype W'.mkQ :=
  LinearMap.exact_subtype_mkQ W'.toSubmodule

end Quotient

end Subrepresentation

namespace Representation

variable {F G S V₁ V₂ V₃ : Type*} [Field F] [Group G] [CommRing S] [Algebra F S]
  [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂] [AddCommGroup V₃] [Module F V₃]
  {ρ₁ : Representation F G V₁} {ρ₂ : Representation F G V₂} {ρ₃ : Representation F G V₃}

/-! ### Left exactness -/

section LeftExact

variable {act : G → S →ₐ[F] S} {H : Subgroup G}

/-- `S ⊗ f` is injective for an injective `f`, as `S` is flat over the field `F`. -/
private theorem baseChange_injective {f : ρ₁.IntertwiningMap ρ₂} (hf : Function.Injective f) :
    Function.Injective (f.toLinearMap.baseChange S) := by
  rw [LinearMap.baseChange_eq_lTensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hf

/-- **`D_S` preserves injectivity**: if the intertwining map `f` is injective, so is `D_S(f)`. -/
theorem periodsMap_injective {f : ρ₁.IntertwiningMap ρ₂} (hf : Function.Injective f) :
    Function.Injective (periodsMap act H f) := fun x y hxy =>
  Subtype.ext (baseChange_injective hf (by simpa using congrArg Subtype.val hxy))

/-- **`D_S` is left exact**: if `0 → V₁ → V₂ → V₃` is exact, that is, `f` is injective and its
image is the kernel of `g`, then the image of `D_S(f)` is the kernel of `D_S(g)`. -/
theorem exact_periodsMap_of_injective {f : ρ₁.IntertwiningMap ρ₂} {g : ρ₂.IntertwiningMap ρ₃}
    (hf : Function.Injective f) (hfg : Function.Exact f g) :
    Function.Exact (periodsMap act H f) (periodsMap act H g) := by
  have hex : Function.Exact (f.toLinearMap.baseChange S) (g.toLinearMap.baseChange S) := by
    rw [LinearMap.baseChange_eq_lTensor, LinearMap.baseChange_eq_lTensor]
    exact Module.Flat.lTensor_exact S hfg
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (hex y).1 (by simpa using congrArg Subtype.val hy)
    refine ⟨⟨x, mem_periods.2 fun γ hγ => baseChange_injective hf ?_⟩, Subtype.ext hx⟩
    rw [← map_baseChange_comm, hx, mem_periods.1 y.2 γ hγ]
  · rintro ⟨x, rfl⟩
    exact Subtype.ext ((hex _).2 ⟨x, rfl⟩)

end LeftExact

/-! ### Direct sums -/

section Prod

variable {act : G → S →ₐ[F] S} {H : Subgroup G}

variable (ρ₁ ρ₂ act H) in
/-- **`D_S(V₁ × V₂) ≃ D_S(V₁) × D_S(V₂)`**: the `S^H`-linear isomorphism given by `D_S` of the
projections, with inverse given by `D_S` of the inclusions. -/
def periodsProdEquiv :
    (ρ₁.prod ρ₂).periods act H ≃ₗ[fixedSubalgebra S act H] ρ₁.periods act H × ρ₂.periods act H :=
  LinearEquiv.ofLinearMap
    ((periodsMap act H (IntertwiningMap.fst F ρ₁ ρ₂)).prod
      (periodsMap act H (IntertwiningMap.snd F ρ₁ ρ₂)))
    ((periodsMap act H (IntertwiningMap.inl F ρ₁ ρ₂)).coprod
      (periodsMap act H (IntertwiningMap.inr F ρ₁ ρ₂)))
    (by
      rw [LinearMap.prod_comp, LinearMap.comp_coprod, LinearMap.comp_coprod, ← periodsMap_comp,
        ← periodsMap_comp, ← periodsMap_comp, ← periodsMap_comp, IntertwiningMap.fst_comp_inl,
        IntertwiningMap.fst_comp_inr, IntertwiningMap.snd_comp_inl,
        IntertwiningMap.snd_comp_inr, periodsMap_id, periodsMap_id, periodsMap_zero,
        periodsMap_zero]
      apply LinearMap.ext
      rintro ⟨x, y⟩
      simp)
    (by
      rw [LinearMap.coprod_comp_prod, ← periodsMap_comp, ← periodsMap_comp, ← periodsMap_add,
        IntertwiningMap.coprod_inl_inr, periodsMap_id])

/-- The first component of `periodsProdEquiv` is `D_S` of the first projection. -/
@[simp]
theorem periodsProdEquiv_apply_fst (x : (ρ₁.prod ρ₂).periods act H) :
    (periodsProdEquiv ρ₁ ρ₂ act H x).1 = periodsMap act H (IntertwiningMap.fst F ρ₁ ρ₂) x :=
  rfl

/-- The second component of `periodsProdEquiv` is `D_S` of the second projection. -/
@[simp]
theorem periodsProdEquiv_apply_snd (x : (ρ₁.prod ρ₂).periods act H) :
    (periodsProdEquiv ρ₁ ρ₂ act H x).2 = periodsMap act H (IntertwiningMap.snd F ρ₁ ρ₂) x :=
  rfl

end Prod

/-! ### Regular rings -/

section Regular

variable [IsDomain S] {act : G →* (S →ₐ[F] S)} {H : Subgroup G}

/-- The corestriction of an intertwining map `f` to its image, a subrepresentation. -/
private def rangeRestrict (f : ρ₁.IntertwiningMap ρ₂) :
    ρ₁.IntertwiningMap f.range.toRepresentation where
  toLinearMap := f.toLinearMap.rangeRestrict
  isIntertwining' γ := LinearMap.ext fun v => Subtype.ext <| by
    change f (ρ₁ γ v) = ρ₂ γ (f v)
    exact IntertwiningMap.isIntertwining _ _ f γ v

namespace IsRegularPeriodRing

/-- **Dimension counting in a short exact sequence** `0 → V₁ → V₂ → V₃ → 0` with `V₂` admissible,
for a regular ring: `V₁` and `V₃` satisfy the dimension form of admissibility and `D_S(g)` is
onto. -/
private theorem exact_aux (hS : IsRegularPeriodRing act H) {f : ρ₁.IntertwiningMap ρ₂}
    {g : ρ₂.IntertwiningMap ρ₃} (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) (h₂ : ρ₂.IsAdmissible act H) :
    ρ₁.IsAdmissible act H ∧ ρ₃.IsAdmissible act H ∧ Function.Surjective (periodsMap act H g) := by
  obtain ⟨hV₂, hd₂⟩ := h₂
  have hV₁ : FiniteDimensional F V₁ := Module.Finite.of_injective f.toLinearMap hf
  have hV₃ : FiniteDimensional F V₃ := Module.Finite.of_surjective g.toLinearMap hg
  let := hS.field
  have := hS.finite_periods ρ₂
  have := hS.finite_periods ρ₃
  have h₁le := hS.finrank_periods_le ρ₁
  have h₃le := hS.finrank_periods_le ρ₃
  -- `dim V₂ = dim V₁ + dim V₃`
  have hdim : Module.finrank F V₁ + Module.finrank F V₃ = Module.finrank F V₂ := by
    have h := LinearMap.finrank_range_add_finrank_ker g.toLinearMap
    rw [LinearMap.range_eq_top.2 hg, finrank_top, (LinearMap.exact_iff.1 hfg),
      LinearMap.finrank_range_of_inj hf] at h
    omega
  -- `dim D_S(V₂) = dim (image of D_S(g)) + dim D_S(V₁)`
  have hrn := LinearMap.finrank_range_add_finrank_ker (K := fixedSubalgebra S act H)
    (V := ρ₂.periods act H) (V₂ := ρ₃.periods act H) (periodsMap act H g)
  rw [LinearMap.exact_iff.1 (exact_periodsMap_of_injective hf hfg),
    LinearMap.finrank_range_of_inj (periodsMap_injective hf)] at hrn
  have hr := Submodule.finrank_le (R := fixedSubalgebra S act H) (M := ρ₃.periods act H)
    (LinearMap.range (periodsMap act H g))
  refine ⟨⟨hV₁, by omega⟩, ⟨hV₃, by omega⟩, ?_⟩
  rw [← LinearMap.range_eq_top]
  exact Submodule.eq_top_of_finrank_eq (K := fixedSubalgebra S act H) (V := ρ₃.periods act H)
    (S := LinearMap.range (periodsMap act H g)) (by omega)

/-- **Subobjects and quotients of admissible representations** (Fontaine–Ouyang, Theorem 3.14 (2);
Fontaine, Exposé III, Proposition 1.5.2 p. 124 and §1.5.3): for a regular ring `S` and a short
exact sequence `0 → V₁ → V₂ → V₃ → 0` of representations (`f` injective, `g` surjective, the image
of `f` the kernel of `g`), if `V₂` is admissible then so are `V₁` and `V₃`. -/
theorem isAdmissible_of_exact (hS : IsRegularPeriodRing act H) {f : ρ₁.IntertwiningMap ρ₂}
    {g : ρ₂.IntertwiningMap ρ₃} (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) (h₂ : ρ₂.IsAdmissible act H) :
    ρ₁.IsAdmissible act H ∧ ρ₃.IsAdmissible act H :=
  ⟨(hS.exact_aux hf hg hfg h₂).1, (hS.exact_aux hf hg hfg h₂).2.1⟩

/-- **`D_S` preserves surjections out of admissible representations**: for a regular ring `S`, if
`g : V₂ → V₃` is surjective and `V₂` is admissible, then `D_S(g)` is surjective. -/
theorem surjective_periodsMap (hS : IsRegularPeriodRing act H) {g : ρ₂.IntertwiningMap ρ₃}
    (hg : Function.Surjective g) (h₂ : ρ₂.IsAdmissible act H) :
    Function.Surjective (periodsMap act H g) :=
  (hS.exact_aux (f := g.ker.subtype) g.ker.subtype_injective hg
    (fun y => ⟨fun hy => ⟨⟨y, hy⟩, rfl⟩, fun ⟨x, hx⟩ => hx ▸ x.2⟩) h₂).2.2

/-- **`D_S` is exact on short exact sequences of admissible representations** (Fontaine–Ouyang,
Theorem 3.14 (2); Fontaine, Exposé III, Proposition 1.5.2 p. 124 and §1.5.3): for a regular ring
`S` and a short exact sequence `0 → V₁ → V₂ → V₃ → 0` with `V₂` admissible, the sequence
`0 → D_S(V₁) → D_S(V₂) → D_S(V₃) → 0` is exact. -/
theorem shortExact_periodsMap (hS : IsRegularPeriodRing act H) {f : ρ₁.IntertwiningMap ρ₂}
    {g : ρ₂.IntertwiningMap ρ₃} (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) (h₂ : ρ₂.IsAdmissible act H) :
    Function.Injective (periodsMap act H f) ∧
      Function.Exact (periodsMap act H f) (periodsMap act H g) ∧
      Function.Surjective (periodsMap act H g) :=
  ⟨periodsMap_injective hf, exact_periodsMap_of_injective hf hfg, hS.surjective_periodsMap hg h₂⟩

/-- **A subrepresentation of an admissible representation is admissible**, for a regular ring
(Fontaine–Ouyang, Theorem 3.14 (2); Fontaine, Exposé III, Proposition 1.5.2 p. 124). -/
theorem isAdmissible_toRepresentation (hS : IsRegularPeriodRing act H)
    (h : ρ₂.IsAdmissible act H) (W : Subrepresentation ρ₂) :
    W.toRepresentation.IsAdmissible act H :=
  (hS.isAdmissible_of_exact W.subtype_injective W.mkQ_surjective W.exact_subtype_mkQ h).1

/-- **A quotient of an admissible representation is admissible**, for a regular ring
(Fontaine–Ouyang, Theorem 3.14 (2); Fontaine, Exposé III, Proposition 1.5.2 p. 124). -/
theorem isAdmissible_quotient (hS : IsRegularPeriodRing act H) (h : ρ₂.IsAdmissible act H)
    (W : Subrepresentation ρ₂) : W.quotient.IsAdmissible act H :=
  (hS.isAdmissible_of_exact W.subtype_injective W.mkQ_surjective W.exact_subtype_mkQ h).2

/-- **Direct sums of admissible representations** (Fontaine–Ouyang, Theorem 3.14 (2); Fontaine,
Exposé III, Proposition 1.5.2 p. 124 and §1.5.3): for a regular ring `S`, `V₁ × V₂` is admissible
if and only if `V₁` and `V₂` are. -/
theorem isAdmissible_prod_iff (hS : IsRegularPeriodRing act H) :
    (ρ₁.prod ρ₂).IsAdmissible act H ↔ ρ₁.IsAdmissible act H ∧ ρ₂.IsAdmissible act H := by
  refine ⟨fun h => hS.isAdmissible_of_exact (f := IntertwiningMap.inl F ρ₁ ρ₂)
    (g := IntertwiningMap.snd F ρ₁ ρ₂) LinearMap.inl_injective
    (IntertwiningMap.snd_surjective ρ₁ ρ₂)
    (fun x => ⟨fun hx => ⟨x.1, Prod.ext rfl hx.symm⟩, fun ⟨y, hy⟩ => hy ▸ rfl⟩) h,
    fun ⟨⟨hV₁, hd₁⟩, ⟨hV₂, hd₂⟩⟩ => ⟨inferInstance, ?_⟩⟩
  have := hS.free_periods ρ₁
  have := hS.free_periods ρ₂
  have := hS.finite_periods ρ₁
  have := hS.finite_periods ρ₂
  rw [LinearEquiv.finrank_eq (periodsProdEquiv ρ₁ ρ₂ act H), Module.finrank_prod,
    Module.finrank_prod, hd₁, hd₂]

/-- **`D_S` is exact on admissible representations** (Fontaine–Ouyang, Theorem 3.14 (2); Fontaine,
Exposé III, Proposition 1.5.2 p. 124): for a regular ring `S`, if `V₁ → V₂ → V₃` is exact (the
image of `f` is the kernel of `g`) and `V₁` is admissible, then
`D_S(V₁) → D_S(V₂) → D_S(V₃)` is exact. -/
theorem exact_periodsMap (hS : IsRegularPeriodRing act H) {f : ρ₁.IntertwiningMap ρ₂}
    {g : ρ₂.IntertwiningMap ρ₃} (hfg : Function.Exact f g) (h₁ : ρ₁.IsAdmissible act H) :
    Function.Exact (periodsMap act H f) (periodsMap act H g) := by
  have hcomp : f = f.range.subtype.comp (rangeRestrict f) :=
    IntertwiningMap.ext (LinearMap.ext fun _ => rfl)
  have hsurj := hS.surjective_periodsMap (g := rangeRestrict f)
    (LinearMap.surjective_rangeRestrict f.toLinearMap) h₁
  have hex := exact_periodsMap_of_injective (act := act) (H := H) f.range.subtype_injective
    (g := g) fun y => (hfg y).trans ⟨fun ⟨x, hx⟩ => ⟨⟨y, x, hx⟩, rfl⟩,
      fun ⟨⟨_, x, hx⟩, hy⟩ => ⟨x, hx.trans hy⟩⟩
  intro y
  rw [hex y]
  conv_rhs => rw [hcomp]
  rw [periodsMap_comp, LinearMap.coe_comp, Set.range_comp, hsurj.range_eq, Set.image_univ]

/-- `w ↦ 1 ⊗ w` from `V` to `S ⊗_F V` is injective, as `F → S` is injective and `V` is flat. -/
private theorem one_tmul_injective : Function.Injective fun v : V₂ => (1 : S) ⊗ₜ[F] v := by
  have h := (Module.Flat.rTensor_preserves_injective_linearMap (M := V₂) (Algebra.linearMap F S)
    (algebraMap F S).injective).comp (_root_.TensorProduct.lid F V₂).symm.injective
  convert h using 1
  funext v
  simp

/-- **`D_S` is faithful on admissible representations** (Fontaine–Ouyang, Theorem 3.14 (2);
Fontaine, Exposé III, Proposition 1.5.2 p. 124): for a regular ring `S`, two intertwining maps
`f, f'` out of an admissible representation with `D_S(f) = D_S(f')` are equal. -/
theorem eq_of_periodsMap_eq (hS : IsRegularPeriodRing act H) (h₁ : ρ₁.IsAdmissible act H)
    {f f' : ρ₁.IntertwiningMap ρ₂} (h : periodsMap act H f = periodsMap act H f') : f = f' := by
  have := h₁.1
  have hspan : Submodule.span S (ρ₁.periods act H : Set (S ⊗[F] V₁)) = ⊤ := by
    rw [← range_comparison, LinearMap.range_eq_top.2
      ((hS.isAdmissible_iff_comparison_bijective ρ₁).1 h₁).2]
  have hS' : f.toLinearMap.baseChange S = f'.toLinearMap.baseChange S :=
    LinearMap.ext_on hspan fun x hx => by
      simpa using congrArg Subtype.val (LinearMap.congr_fun h ⟨x, hx⟩)
  refine IntertwiningMap.ext (LinearMap.ext fun v => one_tmul_injective (F := F) (S := S) ?_)
  simpa using LinearMap.congr_fun hS' ((1 : S) ⊗ₜ[F] v)

end IsRegularPeriodRing

end Regular

end Representation
