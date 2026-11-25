/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RepresentationTheory.GroupCohomology.Corestriction
import MathlibExt.NumberTheory.ModularForms.CoeffHecke

open CategoryTheory groupCohomology

universe u

/-- Unfolding: corestriction on cocycles agrees pointwise with `cor₂`. -/
example {k G : Type u} [CommRing k] [Group G] {H : Subgroup G} [H.FiniteIndex]
    (A : Rep k G) (τ : groupCohomology.Cores.Transversal H)
    (u : cocycles₂ (Rep.res H.subtype A)) :
    (groupCohomology.Cores.corCocycles₂ A τ u : G × G → A) =
      groupCohomology.Cores.cor₂ A τ u :=
  groupCohomology.Cores.coe_corCocycles₂ A τ u

/-- Identity case: for `H = ⊤`, `cor₂` returns the cochain itself, for every representation,
transversal and cochain. -/
example {k G : Type u} [CommRing k] [Group G] (A : Rep k G)
    (τ : Cores.Transversal (⊤ : Subgroup G))
    (u : (⊤ : Subgroup G) × (⊤ : Subgroup G) → A) (g₁ g₂ : G) :
    Cores.cor₂ A τ u (g₁, g₂) = u (⟨g₁, Subgroup.mem_top g₁⟩, ⟨g₂, Subgroup.mem_top g₂⟩) := by
  have := QuotientGroup.subsingleton_quotient_top (G := G)
  let _ : Fintype (G ⧸ (⊤ : Subgroup G)) := Cores.fintypeQuot
  have h₁ : τ.lam g₁ = ⟨g₁, Subgroup.mem_top g₁⟩ := τ.lam_of_mem ⟨g₁, Subgroup.mem_top g₁⟩
  have h₂ : τ.lam (g₁ * g₂) = ⟨g₁ * g₂, Subgroup.mem_top _⟩ :=
    τ.lam_of_mem ⟨g₁ * g₂, Subgroup.mem_top _⟩
  rw [Cores.cor₂_apply, Fintype.sum_subsingleton _ ((1 : G) : G ⧸ ⊤), τ.σ_one, map_one, inv_one,
    one_mul, one_apply_eq_self, h₁, h₂]
  congr 2
  exact Subtype.ext (by simp)

/-! ### A proper subgroup

`C₄ = ⟨r⟩` is cyclic of order four, `H = {1, r²}` has index two, and the transversal is `{1, r}`.
`C₄` acts on `ZMod 5` by the faithful character `r ↦ 2`, so `H` acts by `-1` and
`ρ(r) ≠ ρ(r⁻¹)`. -/

/-- The cyclic group of order four, written multiplicatively. -/
abbrev C₄ := Multiplicative (ZMod 4)

/-- The generator `r` of `C₄`. -/
def gen : C₄ := Multiplicative.ofAdd 1

/-- The subgroup `{1, r²}` of `C₄`: the even exponents. -/
def evenSub : Subgroup C₄ where
  carrier := {x | (Multiplicative.toAdd x).val % 2 = 0}
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

lemma mem_evenSub {x : C₄} : x ∈ evenSub ↔ (Multiplicative.toAdd x).val % 2 = 0 := Iff.rfl

instance : DecidablePred (· ∈ evenSub) := fun _ => decidable_of_iff _ mem_evenSub.symm

/-- The element `r²` of `evenSub`. -/
def genSq : evenSub := ⟨gen * gen, by decide⟩

/-- The representative, `1` or `r`, of the coset of `x`: the parity of its exponent. -/
def rep (x : C₄) : C₄ := Multiplicative.ofAdd (((Multiplicative.toAdd x).val % 2 : ℕ) : ZMod 4)

/-- The transversal `{1, r}` of `evenSub`. -/
def τ₄ : Cores.Transversal evenSub where
  σ := Quotient.lift rep fun a b hab => by
    have h := QuotientGroup.leftRel_apply.mp hab
    clear hab
    revert a b
    decide
  mk_σ q := by
    refine QuotientGroup.induction_on q fun x => ?_
    change ((rep x : C₄) : C₄ ⧸ evenSub) = x
    rw [QuotientGroup.eq]
    revert x
    decide
  σ_one := by decide

/-- The character of `C₄` on `ZMod 5` with `r ↦ 2`. -/
def ρ₄ : Representation (ZMod 5) C₄ (ZMod 5) where
  toFun x := (2 : ZMod 5) ^ (Multiplicative.toAdd x).val • LinearMap.id
  map_one' := by
    ext
    simp
  map_mul' a b := by
    ext
    simp only [LinearMap.smul_apply, LinearMap.id_apply, mul_apply_eq_comp, smul_eq_mul, mul_one]
    revert a b
    decide

/-- `ZMod 5` as a representation of `C₄` through `ρ₄`. -/
abbrev A₄ : Rep (ZMod 5) C₄ := Rep.of ρ₄

lemma A₄_ρ_gen (y : ZMod 5) : A₄.ρ gen y = 2 * y := by
  revert y
  decide

/-- Every coset of `evenSub` is the coset of `1` or of `r`. -/
lemma mk_cases (q : C₄ ⧸ evenSub) :
    q = ((1 : C₄) : C₄ ⧸ evenSub) ∨ q = ((gen : C₄) : C₄ ⧸ evenSub) := by
  refine QuotientGroup.induction_on q fun x => ?_
  rw [QuotientGroup.eq, QuotientGroup.eq]
  revert x
  decide

lemma mk_one_ne_mk_gen : ((1 : C₄) : C₄ ⧸ evenSub) ≠ ((gen : C₄) : C₄ ⧸ evenSub) := by
  rw [Ne, QuotientGroup.eq]
  decide

/-- `cor₂` along `evenSub ≤ C₄` with the transversal `{1, r}`: one term for each coset. -/
lemma cor₂_τ₄ (u : evenSub × evenSub → ZMod 5) (g₁ g₂ : C₄) :
    Cores.cor₂ A₄ τ₄ u (g₁, g₂) =
      u (τ₄.lam g₁, (τ₄.lam g₁)⁻¹ * τ₄.lam (g₁ * g₂)) +
        2 * u (τ₄.lam (gen⁻¹ * g₁), (τ₄.lam (gen⁻¹ * g₁))⁻¹ * τ₄.lam (gen⁻¹ * g₁ * g₂)) := by
  have hσ : τ₄.σ ((gen : C₄) : C₄ ⧸ evenSub) = gen := by decide
  let _ : Fintype (C₄ ⧸ evenSub) := Cores.fintypeQuot
  rw [Cores.cor₂_apply, Fintype.sum_eq_add _ _ mk_one_ne_mk_gen
      fun q hq => ((mk_cases q).elim hq.1 hq.2).elim,
    τ₄.σ_one, hσ, map_one, inv_one, one_apply_eq_self, A₄_ρ_gen]
  simp only [one_mul]

/-- `cor₂` at `(r, r)`, for every cochain `u` of `evenSub`: the two terms come from the cosets of
`1` and `r`, the second one acted on by `ρ(r) = 2`. -/
example (u : evenSub × evenSub → ZMod 5) :
    Cores.cor₂ A₄ τ₄ u (gen, gen) = u (genSq, 1) + 2 * u (1, genSq) := by
  have e₁ : (τ₄.lam gen, (τ₄.lam gen)⁻¹ * τ₄.lam (gen * gen)) = (genSq, 1) := by decide
  have e₂ : (τ₄.lam (gen⁻¹ * gen), (τ₄.lam (gen⁻¹ * gen))⁻¹ * τ₄.lam (gen⁻¹ * gen * gen)) =
      (1, genSq) := by decide
  rw [cor₂_τ₄, e₁, e₂]

/-- `cor₂` at `(r, r²)`, for every cochain `u` of `evenSub`. -/
example (u : evenSub × evenSub → ZMod 5) :
    Cores.cor₂ A₄ τ₄ u (gen, gen * gen) = u (genSq, genSq) + 2 * u (1, genSq) := by
  have e₁ : (τ₄.lam gen, (τ₄.lam gen)⁻¹ * τ₄.lam (gen * (gen * gen))) = (genSq, genSq) := by
    decide
  have e₂ : (τ₄.lam (gen⁻¹ * gen),
      (τ₄.lam (gen⁻¹ * gen))⁻¹ * τ₄.lam (gen⁻¹ * gen * (gen * gen))) = (1, genSq) := by decide
  rw [cor₂_τ₄, e₁, e₂]

/-- `cor₂` at `(r³, r)`, for every cochain `u` of `evenSub`. -/
example (u : evenSub × evenSub → ZMod 5) :
    Cores.cor₂ A₄ τ₄ u (gen⁻¹, gen) = u (1, 1) + 2 * u (genSq, genSq) := by
  have e₁ : (τ₄.lam gen⁻¹, (τ₄.lam gen⁻¹)⁻¹ * τ₄.lam (gen⁻¹ * gen)) = (1, 1) := by decide
  have e₂ : (τ₄.lam (gen⁻¹ * gen⁻¹),
      (τ₄.lam (gen⁻¹ * gen⁻¹))⁻¹ * τ₄.lam (gen⁻¹ * gen⁻¹ * gen)) = (genSq, genSq) := by decide
  rw [cor₂_τ₄, e₁, e₂]

/-- A concrete 2-cocycle of `evenSub` with values in `A₄`: `1` on `{1} × H` and `-1` on
`{r²} × H`. -/
noncomputable def u₀ : cocycles₂ (Rep.res evenSub.subtype A₄) :=
  ⟨fun hh => if (hh.1 : C₄) = 1 then 1 else -1, by
    rw [mem_cocycles₂_iff]
    decide⟩

/-- The corestriction of `u₀` takes the values `3, 1, 2, 4` at `(g₁, g₂)` for `g₁ = 1, r, r², r³`,
whatever `g₂`. The proof only splits the sum over the two cosets and evaluates. -/
example (g₁ g₂ : C₄) :
    (Cores.corCocycles₂ A₄ τ₄ u₀ : C₄ × C₄ → A₄) (g₁, g₂) =
      ![(3 : ZMod 5), 1, 2, 4] (Multiplicative.toAdd g₁) := by
  let _ : Fintype (C₄ ⧸ evenSub) := Cores.fintypeQuot
  rw [Cores.coe_corCocycles₂, Cores.cor₂_apply, Fintype.sum_eq_add _ _ mk_one_ne_mk_gen
    fun q hq => ((mk_cases q).elim hq.1 hq.2).elim]
  revert g₁ g₂
  decide

/-- A cochain that separates its two arguments: `u₁ (h₁, h₂) = 2 [h₁ = r²] + [h₂ = r²]`. -/
def u₁ (hh : evenSub × evenSub) : ZMod 5 :=
  (if (hh.1 : C₄) = 1 then 0 else 2) + if (hh.2 : C₄) = 1 then 0 else 1

/-- All sixteen values of `cor₂ u₁`: row `g₁`, column `g₂`, by exponent. The proof only splits the
sum over the two cosets and evaluates. -/
example (g₁ g₂ : C₄) :
    Cores.cor₂ A₄ τ₄ u₁ (g₁, g₂) =
      ![![(0 : ZMod 5), 1, 3, 2], ![2, 4, 0, 3], ![1, 2, 4, 3], ![4, 1, 2, 0]]
        (Multiplicative.toAdd g₁) (Multiplicative.toAdd g₂) := by
  let _ : Fintype (C₄ ⧸ evenSub) := Cores.fintypeQuot
  rw [Cores.cor₂_apply, Fintype.sum_eq_add _ _ mk_one_ne_mk_gen
    fun q hq => ((mk_cases q).elim hq.1 hq.2).elim]
  revert g₁ g₂
  decide

/-- Degree one, trivial coefficients: `cor₁` of a homomorphism `φ : H → A` is `coresHom H φ`, i.e.
Mathlib's transfer, for every transversal. -/
example {k G : Type u} [CommRing k] [Group G] {H : Subgroup G} [H.FiniteIndex]
    (A : Type u) [AddCommGroup A] [Module k A] (τ : Cores.Transversal H)
    (φ : Additive H →+ A) (g : G) :
    Cores.cor₁ (Rep.trivial k G A) τ (fun h => φ (Additive.ofMul h)) g =
      HeckeEis.coresHom H φ (Additive.ofMul g) := by
  let T : H.LeftTransversal := ⟨Set.range τ.σ, Subgroup.isComplement_range_left τ.mk_σ⟩
  have hT : ∀ q : G ⧸ H, (T.2.leftQuotientEquiv q : G) = τ.σ q :=
    Subgroup.IsComplement.leftQuotientEquiv_apply τ.mk_σ
  rw [HeckeEis.coresHom_eq_transfer, MonoidHom.coe_toAdditiveLeft, Function.comp_apply,
    Function.comp_apply, toMul_ofMul, MonoidHom.transfer_def _ T g,
    Subgroup.leftTransversals.diff, toAdd_prod, Cores.cor₁_apply]
  refine Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) fun q _ => ?_
  rw [Rep.trivial_ρ_apply]
  simp only [AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd]
  congr 2
  ext
  rw [Cores.Transversal.coe_lam, Cores.Transversal.qinv_σ_inv_mul, Subgroup.coe_mk, hT,
    Subgroup.smul_apply_eq_smul_apply_inv_smul, hT, smul_eq_mul, mul_assoc]

/-- The corestriction API is available in a higher universe. -/
example {k G : Type (u + 1)} [CommRing k] [Group G] {H : Subgroup G}
    [H.FiniteIndex] (A : Rep k G) (τ : groupCohomology.Cores.Transversal H)
    (u : cocycles₂ (Rep.res H.subtype A)) :
    groupCohomology.Cores.cores A τ (H2π _ u) =
      H2π A (groupCohomology.Cores.corCocycles₂ A τ u) :=
  groupCohomology.Cores.cores_H2π A τ u
