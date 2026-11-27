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
theorem cor₂_top {k G : Type u} [CommRing k] [Group G] (A : Rep k G)
    (τ : Cores.Transversal (⊤ : Subgroup G))
    (u : (⊤ : Subgroup G) × (⊤ : Subgroup G) → A) (g₁ g₂ : G) :
    Cores.cor₂ A τ u (g₁, g₂) = u (⟨g₁, Subgroup.mem_top g₁⟩, ⟨g₂, Subgroup.mem_top g₂⟩) := by
  have := QuotientGroup.subsingleton_quotient_top (G := G)
  let _ : Fintype (G ⧸ (⊤ : Subgroup G)) := Subgroup.fintypeQuotientOfFiniteIndex
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
  let _ : Fintype (C₄ ⧸ evenSub) := Subgroup.fintypeQuotientOfFiniteIndex
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
  let _ : Fintype (C₄ ⧸ evenSub) := Subgroup.fintypeQuotientOfFiniteIndex
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
  let _ : Fintype (C₄ ⧸ evenSub) := Subgroup.fintypeQuotientOfFiniteIndex
  rw [Cores.cor₂_apply, Fintype.sum_eq_add _ _ mk_one_ne_mk_gen
    fun q hq => ((mk_cases q).elim hq.1 hq.2).elim]
  revert g₁ g₂
  decide

/-! ### Nonzero classes

Both cohomology groups above vanish, since `2` and `4` are invertible in `ZMod 5`. The tests
below use trivial coefficients `ZMod p` for a prime `p` dividing the group order, where a
2-coboundary `d φ` sums to `|G| • φ x = 0` over its first argument; a cocycle with a nonzero
such sum therefore has a nonzero class. -/

/-- Summing a 2-coboundary `d φ` of a finite group acting trivially over its first argument
gives `|G| • φ x`. -/
lemma sum_d₁₂_trivial {k G : Type} [CommRing k] [Group G] [Fintype G] (φ : G → k) (x : G) :
    ∑ g : G, (d₁₂ (Rep.trivial k G k)).hom φ (g, x) = Fintype.card G • φ x := by
  simp only [d₁₂_hom_apply, Representation.trivial_apply, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
  rw [Fintype.sum_equiv (Equiv.mulRight x) (fun g => φ (g * x)) φ fun _ => rfl, sub_add_cancel]

/-- If `|G| = 0` in `k`, a 2-cochain of `G` with values in the trivial representation `k` whose
sum over the first argument is nonzero at some `x` is not a coboundary. -/
lemma not_mem_coboundaries₂ {k G : Type} [CommRing k] [Group G] [Fintype G]
    (hG : (Fintype.card G : k) = 0) (F : G × G → k) (x : G) (hF : ∑ g : G, F (g, x) ≠ 0) :
    F ∉ coboundaries₂ (Rep.trivial k G k) := by
  rintro ⟨φ, rfl⟩
  exact hF (by rw [sum_d₁₂_trivial, nsmul_eq_mul, hG, zero_mul])

/-! #### The carry cocycle of `C₂`, with `H = ⊤`

`C₂ = ⟨r⟩` acts trivially on `ZMod 2`. The carry cocycle, `1` at `(r, r)` and `0` elsewhere,
represents the nonzero class of `H²(C₂, ZMod 2)`, that of the extension `ZMod 4`. -/

/-- The cyclic group of order two, written multiplicatively. -/
abbrev C₂ := Multiplicative (ZMod 2)

/-- `ZMod 2` with the trivial action of `C₂`. -/
abbrev T₂ : Rep (ZMod 2) C₂ := Rep.trivial (ZMod 2) C₂ (ZMod 2)

/-- The carry cocycle of `C₂`: `1` at `(r, r)`, `0` elsewhere. -/
noncomputable def carry₂ : cocycles₂ T₂ :=
  ⟨fun gg => if gg.1 ≠ 1 ∧ gg.2 ≠ 1 then 1 else 0, by
    rw [mem_cocycles₂_iff]
    decide⟩

/-- The restriction of `carry₂` to `⊤`. -/
noncomputable def carryTop : cocycles₂ (Rep.res (⊤ : Subgroup C₂).subtype T₂) :=
  ⟨fun hh => carry₂ ((hh.1 : C₂), (hh.2 : C₂)), Cores.res_mem_cocycles₂ T₂ carry₂.2⟩

/-- The class of `carry₂` is nonzero: `carry₂ (1, r) + carry₂ (r, r) = 1`. -/
lemma H2π_carry₂_ne_zero : H2π T₂ carry₂ ≠ 0 := by
  rw [Ne, H2π_eq_zero_iff]
  exact not_mem_coboundaries₂ (by decide) _ (Multiplicative.ofAdd 1) (by decide)

/-- `cores` sends the class of `carryTop` to the class of `carry₂`, for every transversal of
`⊤`. -/
lemma cores_carryTop (τ : Cores.Transversal (⊤ : Subgroup C₂)) :
    Cores.cores T₂ τ (H2π _ carryTop) = H2π T₂ carry₂ := by
  rw [Cores.cores_H2π]
  exact congrArg (H2π T₂) (cocycles₂_ext fun g₁ g₂ => cor₂_top T₂ τ carryTop g₁ g₂)

/-- The class of `carryTop` is nonzero, and so is its corestriction. -/
example (τ : Cores.Transversal (⊤ : Subgroup C₂)) :
    H2π _ carryTop ≠ 0 ∧ Cores.cores T₂ τ (H2π _ carryTop) ≠ 0 := by
  refine ⟨fun h => H2π_carry₂_ne_zero ?_, by rw [cores_carryTop]; exact H2π_carry₂_ne_zero⟩
  rw [← cores_carryTop τ, h, map_zero]

/-! #### A proper subgroup and two transversals

`C₆ = ⟨r⟩` acts trivially on `ZMod 3`, and `K = {1, r², r⁴}` has index two. The carry cocycle of
`C₆` restricts to the carry cocycle of `K ≅ C₃`. Its corestrictions for the transversals
`{1, r}` and `{1, r³}` are different cocycles with the same class, and that class is nonzero. -/

/-- The cyclic group of order six, written multiplicatively. -/
abbrev C₆ := Multiplicative (ZMod 6)

/-- The generator `r` of `C₆`. -/
def gen₆ : C₆ := Multiplicative.ofAdd 1

/-- The subgroup `{1, r², r⁴}` of `C₆`: the even exponents. -/
def evenSub₆ : Subgroup C₆ where
  carrier := {x | (Multiplicative.toAdd x).val % 2 = 0}
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

lemma mem_evenSub₆ {x : C₆} : x ∈ evenSub₆ ↔ (Multiplicative.toAdd x).val % 2 = 0 := Iff.rfl

instance : DecidablePred (· ∈ evenSub₆) := fun _ => decidable_of_iff _ mem_evenSub₆.symm

/-- The representative, `1` or `r`, of the coset of `x`. -/
def rep₆ (x : C₆) : C₆ := Multiplicative.ofAdd (((Multiplicative.toAdd x).val % 2 : ℕ) : ZMod 6)

/-- The representative, `1` or `r³`, of the coset of `x`. -/
def rep₆' (x : C₆) : C₆ :=
  Multiplicative.ofAdd (((Multiplicative.toAdd x).val % 2 * 3 : ℕ) : ZMod 6)

/-- The transversal `{1, r}` of `evenSub₆`. -/
def τ₆ : Cores.Transversal evenSub₆ where
  σ := Quotient.lift rep₆ fun a b hab => by
    have h := QuotientGroup.leftRel_apply.mp hab
    clear hab
    revert a b
    decide
  mk_σ q := by
    refine QuotientGroup.induction_on q fun x => ?_
    change ((rep₆ x : C₆) : C₆ ⧸ evenSub₆) = x
    rw [QuotientGroup.eq]
    revert x
    decide
  σ_one := by decide

/-- The transversal `{1, r³}` of `evenSub₆`. -/
def τ₆' : Cores.Transversal evenSub₆ where
  σ := Quotient.lift rep₆' fun a b hab => by
    have h := QuotientGroup.leftRel_apply.mp hab
    clear hab
    revert a b
    decide
  mk_σ q := by
    refine QuotientGroup.induction_on q fun x => ?_
    change ((rep₆' x : C₆) : C₆ ⧸ evenSub₆) = x
    rw [QuotientGroup.eq]
    revert x
    decide
  σ_one := by decide

/-- Every coset of `evenSub₆` is the coset of `1` or of `r`. -/
lemma mk_cases₆ (q : C₆ ⧸ evenSub₆) :
    q = ((1 : C₆) : C₆ ⧸ evenSub₆) ∨ q = ((gen₆ : C₆) : C₆ ⧸ evenSub₆) := by
  refine QuotientGroup.induction_on q fun x => ?_
  rw [QuotientGroup.eq, QuotientGroup.eq]
  revert x
  decide

lemma mk_one_ne_mk_gen₆ : ((1 : C₆) : C₆ ⧸ evenSub₆) ≠ ((gen₆ : C₆) : C₆ ⧸ evenSub₆) := by
  rw [Ne, QuotientGroup.eq]
  decide

/-- `ZMod 3` with the trivial action of `C₆`. -/
abbrev T₃ : Rep (ZMod 3) C₆ := Rep.trivial (ZMod 3) C₆ (ZMod 3)

/-- The carry cocycle of `C₆`: `1` at `(rⁱ, rʲ)` with `0 ≤ i, j < 6` and `i + j ≥ 6`, `0`
elsewhere. -/
noncomputable def carry₆ : cocycles₂ T₃ :=
  ⟨fun gg => if 6 ≤ (Multiplicative.toAdd gg.1).val + (Multiplicative.toAdd gg.2).val then 1
    else 0, by
    rw [mem_cocycles₂_iff]
    decide⟩

/-- The restriction of `carry₆` to `evenSub₆`: the carry cocycle of `evenSub₆ ≅ C₃`. -/
noncomputable def carryK : cocycles₂ (Rep.res evenSub₆.subtype T₃) :=
  ⟨fun hh => carry₆ ((hh.1 : C₆), (hh.2 : C₆)), Cores.res_mem_cocycles₂ T₃ carry₆.2⟩

/-- All 36 values of `cor₂ carryK` for the transversal `{1, r}`: row `g₁`, column `g₂`, by
exponent. The proof only splits the sum over the two cosets and evaluates. -/
lemma cor₂_τ₆ (g₁ g₂ : C₆) :
    Cores.cor₂ T₃ τ₆ carryK (g₁, g₂) =
      ![![(0 : ZMod 3), 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 1], ![0, 0, 0, 1, 2, 1],
        ![0, 0, 1, 2, 2, 1], ![0, 1, 2, 2, 2, 1], ![0, 1, 1, 1, 1, 0]]
        (Multiplicative.toAdd g₁) (Multiplicative.toAdd g₂) := by
  let _ : Fintype (C₆ ⧸ evenSub₆) := Subgroup.fintypeQuotientOfFiniteIndex
  rw [Cores.cor₂_apply, Fintype.sum_eq_add _ _ mk_one_ne_mk_gen₆
    fun q hq => ((mk_cases₆ q).elim hq.1 hq.2).elim]
  revert g₁ g₂
  decide

/-- All 36 values of `cor₂ carryK` for the transversal `{1, r³}`. -/
lemma cor₂_τ₆' (g₁ g₂ : C₆) :
    Cores.cor₂ T₃ τ₆' carryK (g₁, g₂) =
      ![![(0 : ZMod 3), 0, 0, 0, 0, 0], ![0, 2, 2, 0, 2, 2], ![0, 2, 0, 0, 2, 0],
        ![0, 0, 0, 0, 0, 0], ![0, 2, 2, 0, 2, 2], ![0, 2, 0, 0, 2, 0]]
        (Multiplicative.toAdd g₁) (Multiplicative.toAdd g₂) := by
  let _ : Fintype (C₆ ⧸ evenSub₆) := Subgroup.fintypeQuotientOfFiniteIndex
  rw [Cores.cor₂_apply, Fintype.sum_eq_add _ _ mk_one_ne_mk_gen₆
    fun q hq => ((mk_cases₆ q).elim hq.1 hq.2).elim]
  revert g₁ g₂
  decide

/-- The two transversals give different cocycles: at `(r, r)` the values are `0` and `2`. -/
example : Cores.cor₂ T₃ τ₆ carryK (gen₆, gen₆) ≠ Cores.cor₂ T₃ τ₆' carryK (gen₆, gen₆) := by
  rw [cor₂_τ₆, cor₂_τ₆']
  decide

/-- The two corestrictions of the class of `carryK` agree; that class is nonzero (the values of
`cor₂ carryK` at `(g, r)` sum to `2`), and so is the class of `carryK`. -/
example : Cores.cores T₃ τ₆ (H2π _ carryK) = Cores.cores T₃ τ₆' (H2π _ carryK) ∧
    Cores.cores T₃ τ₆ (H2π _ carryK) ≠ 0 ∧ H2π _ carryK ≠ 0 := by
  have hne : Cores.cores T₃ τ₆ (H2π _ carryK) ≠ 0 := by
    rw [Cores.cores_H2π, Ne, H2π_eq_zero_iff]
    refine not_mem_coboundaries₂ (by decide) _ gen₆ ?_
    simp only [Cores.coe_corCocycles₂, cor₂_τ₆]
    decide
  refine ⟨Cores.cores_eq_cores T₃ τ₆ τ₆' _, hne, fun h => hne ?_⟩
  rw [h, map_zero]

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
