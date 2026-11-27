/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.SuccPred.Int
import Mathlib.Tactic.LinearCombination

/-!
# Decreasing filtrations of vector spaces and their Hodge numbers

A filtered vector space in the sense of Fontaine–Ouyang is a vector space `V` over a field `K`
together with a decreasing, separated and exhaustive `ℤ`-indexed filtration `(Fil^i V)_{i ∈ ℤ}`
by subspaces. Its Hodge number is `t_H(V) = ∑_{i ∈ ℤ} i · dim_K gr^i V`, where
`gr^i V = Fil^i V / Fil^(i+1) V`. Here `t_H` is defined directly by this formula (Fontaine–Ouyang,
Proposition 8.37); `DecreasingFiltration.hodgeNumber_of_finrank_eq_one` recovers their
Definition 8.36 (1) in dimension one.

## Main definitions

* `DecreasingFiltration K V`: a decreasing, separated and exhaustive `ℤ`-indexed filtration of
  the `K`-module `V` by `K`-submodules.
* `DecreasingFiltration.gr`: the graded pieces `gr^i V = Fil^i V / Fil^(i+1) V`.
* `DecreasingFiltration.hodgeNumber`: the Hodge number `t_H(V) = ∑ᵢ i · dim_K gr^i V`.
* `DecreasingFiltration.single`: the filtration with a single jump.
* `DecreasingFiltration.comap`: the filtration induced along an injective linear map.
* `DecreasingFiltration.map`: the quotient filtration along a surjective linear map.

## Main results

* `DecreasingFiltration.exists_fil_eq_bot`, `DecreasingFiltration.exists_fil_eq_top`: on a
  finite-dimensional space the filtration reaches `0` and `V`.
* `DecreasingFiltration.hodgeNumber_eq_sum`: if `a ≤ b`, `Fil^a V = V` and `Fil^b V = 0`, then
  `t_H(V) = a · dim_K V + ∑_{a < i < b} dim_K Fil^i V`.
* `DecreasingFiltration.hodgeNumber_of_finrank_eq_one`: in dimension one, `t_H(V)` is the
  integer `i` with `Fil^i V = V` and `Fil^(i+1) V = 0`; in dimension zero it is `0`
  (`DecreasingFiltration.hodgeNumber_eq_zero_of_finrank_eq_zero`).
* `DecreasingFiltration.hodgeNumber_eq_add_of_exact`: the Hodge number is additive in short exact
  sequences, with the induced filtration on the kernel and the quotient filtration on the
  cokernel.
* `DecreasingFiltration.hodgeNumber_le_of_le`, `DecreasingFiltration.eq_of_le_of_hodgeNumber_le`:
  the Hodge number is monotone in the filtration, and two comparable filtrations with the same
  Hodge number are equal.
* `DecreasingFiltration.comap_map_eq_map_comap`: induced and quotient filtrations commute across
  a commutative square.

## References

* J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations* (book draft, 2022),
  §6.2.4 and §8.2.4 (Definition 8.36, Propositions 8.37 and 8.38 (1)).
* J.-M. Fontaine, *Représentations p-adiques semi-stables*, Astérisque 223 (1994), Exposé III,
  §4.4.1 p. 150.
-/

@[expose] public section

open Module

variable {K : Type*} [Field K] {V W U V' V'' W'' : Type*}
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
  [AddCommGroup V'] [Module K V'] [AddCommGroup V''] [Module K V'']
  [AddCommGroup W''] [Module K W'']

/-- A decreasing, separated and exhaustive `ℤ`-indexed filtration of the `K`-module `V` by
`K`-submodules `Fil^i V`: `Fil^j V ≤ Fil^i V` whenever `i ≤ j`, `⨅ i, Fil^i V = ⊥` (so
`⋂ᵢ Fil^i V = 0`) and `⨆ i, Fil^i V = ⊤` (so `⋃ᵢ Fil^i V = V`, the family being directed).
This is a filtered vector space in the sense of Fontaine–Ouyang, §6.2.4. -/
structure DecreasingFiltration (K V : Type*) [Field K] [AddCommGroup V] [Module K V] where
  /-- The `i`-th step `Fil^i V`. -/
  Fil : ℤ → Submodule K V
  /-- Decreasing: `Fil^j V ≤ Fil^i V` whenever `i ≤ j`. -/
  antitone : Antitone Fil
  /-- Separated: `⋂ᵢ Fil^i V = 0`. -/
  iInf_eq_bot : ⨅ i, Fil i = ⊥
  /-- Exhaustive: `⋃ᵢ Fil^i V = V`. -/
  iSup_eq_top : ⨆ i, Fil i = ⊤

namespace DecreasingFiltration

/-- Two filtrations `F` and `G` of `V` are equal if `F.Fil i = G.Fil i` for every `i : ℤ`. -/
@[ext]
theorem ext {F G : DecreasingFiltration K V} (h : ∀ i, F.Fil i = G.Fil i) : F = G := by
  cases F
  cases G
  congr
  exact funext h

/-- If `Fil^j V = V` and `i ≤ j`, then `Fil^i V = V`. -/
theorem fil_eq_top_of_le (F : DecreasingFiltration K V) {i j : ℤ} (hj : F.Fil j = ⊤)
    (hij : i ≤ j) : F.Fil i = ⊤ :=
  top_unique (hj.symm.trans_le (F.antitone hij))

/-- If `Fil^i V = 0` and `i ≤ j`, then `Fil^j V = 0`. -/
theorem fil_eq_bot_of_le (F : DecreasingFiltration K V) {i j : ℤ} (hi : F.Fil i = ⊥)
    (hij : i ≤ j) : F.Fil j = ⊥ :=
  bot_unique ((F.antitone hij).trans_eq hi)

/-- If `V` is finite-dimensional, then some step of the filtration vanishes: `Fil^i V = 0` for
some `i : ℤ`. -/
theorem exists_fil_eq_bot [FiniteDimensional K V] (F : DecreasingFiltration K V) :
    ∃ i, F.Fil i = ⊥ := by
  classical
  have h : ∃ n, ∃ i, finrank K (F.Fil i) = n := ⟨_, 0, rfl⟩
  obtain ⟨i₀, hi₀⟩ := Nat.find_spec h
  refine ⟨i₀, eq_bot_iff.2 ?_⟩
  rw [← F.iInf_eq_bot]
  refine le_iInf fun j => ?_
  rcases le_total i₀ j with hij | hij
  · exact (Submodule.eq_of_le_of_finrank_le (F.antitone hij)
      (hi₀.trans_le (Nat.find_min' h ⟨j, rfl⟩))).ge
  · exact F.antitone hij

/-- If `V` is finite-dimensional, then some step of the filtration is the whole space:
`Fil^i V = V` for some `i : ℤ`. -/
theorem exists_fil_eq_top [FiniteDimensional K V] (F : DecreasingFiltration K V) :
    ∃ i, F.Fil i = ⊤ := by
  classical
  have h : ∃ n, ∃ i, finrank K V - finrank K (F.Fil i) = n := ⟨_, 0, rfl⟩
  obtain ⟨i₀, hi₀⟩ := Nat.find_spec h
  refine ⟨i₀, eq_top_iff.2 ?_⟩
  rw [← F.iSup_eq_top]
  refine iSup_le fun j => ?_
  rcases le_total i₀ j with hij | hij
  · exact F.antitone hij
  · refine (Submodule.eq_of_le_of_finrank_le (F.antitone hij) ?_).ge
    have h₁ := Nat.find_min' h ⟨j, rfl⟩
    have h₂ := Submodule.finrank_le (F.Fil j)
    have h₃ := Submodule.finrank_le (F.Fil i₀)
    omega

/-- If `V` is finite-dimensional, then there are integers `a ≤ b` with `Fil^a V = V` and
`Fil^b V = 0`. -/
theorem exists_le_and_fil_eq_top_and_fil_eq_bot [FiniteDimensional K V]
    (F : DecreasingFiltration K V) : ∃ a b, a ≤ b ∧ F.Fil a = ⊤ ∧ F.Fil b = ⊥ := by
  obtain ⟨a, ha⟩ := F.exists_fil_eq_top
  obtain ⟨b, hb⟩ := F.exists_fil_eq_bot
  exact ⟨min a b, b, min_le_right a b, F.fil_eq_top_of_le ha (min_le_left a b), hb⟩

/-- The `i`-th graded piece `gr^i V = Fil^i V / Fil^(i+1) V`: the quotient of `Fil^i V` by
`Fil^(i+1) V`, viewed as a `K`-submodule of `Fil^i V`. -/
abbrev gr (F : DecreasingFiltration K V) (i : ℤ) : Type _ :=
  ↥(F.Fil i) ⧸ (F.Fil (i + 1)).comap (F.Fil i).subtype

/-- If `V` is finite-dimensional, then `dim_K gr^i V = dim_K Fil^i V - dim_K Fil^(i+1) V`, as
integers. -/
theorem finrank_gr [FiniteDimensional K V] (F : DecreasingFiltration K V) (i : ℤ) :
    (finrank K (F.gr i) : ℤ) = finrank K (F.Fil i) - finrank K (F.Fil (i + 1)) := by
  have h₁ : finrank K (F.gr i) + finrank K ((F.Fil (i + 1)).comap (F.Fil i).subtype) =
      finrank K (F.Fil i) :=
    Submodule.finrank_quotient_add_finrank _
  have h₂ := (Submodule.comapSubtypeEquivOfLe (F.antitone (show i ≤ i + 1 by omega))).finrank_eq
  omega

/-- The Hodge number `t_H(V) = ∑_{i ∈ ℤ} i · dim_K gr^i V` of the filtration. It is defined as a
`finsum`, which is `0` if infinitely many terms are nonzero; when `V` is finite-dimensional only
finitely many terms are nonzero, see `hodgeNumber_eq_sum`. -/
noncomputable def hodgeNumber (F : DecreasingFiltration K V) : ℤ :=
  ∑ᶠ i : ℤ, i * (finrank K (F.gr i) : ℤ)

/-- Abel summation over an integer interval: if `a ≤ b` and `d : ℤ → ℤ`, then
`∑_{a ≤ i < b} i (d i - d (i + 1)) + b d b = a d a + ∑_{a < i ≤ b} d i`. -/
private theorem sum_Ico_mul_sub_add (d : ℤ → ℤ) {a b : ℤ} (hab : a ≤ b) :
    ∑ i ∈ Finset.Ico a b, i * (d i - d (i + 1)) + b * d b =
      a * d a + ∑ i ∈ Finset.Ioc a b, d i := by
  obtain ⟨n, rfl⟩ := Int.le.dest hab
  induction n with
  | zero => simp
  | succ n ih =>
    have h : a ≤ a + n := by omega
    rw [Nat.cast_succ, ← add_assoc, ← Finset.insert_Ico_right_eq_Ico_add_one h,
      ← Finset.insert_Ioc_right_eq_Ioc_add_one h,
      Finset.sum_insert (by rw [Finset.mem_Ico]; omega),
      Finset.sum_insert (by rw [Finset.mem_Ioc]; omega)]
    linear_combination ih h

/-- Let `V` be finite-dimensional and let `a ≤ b` be integers with `Fil^a V = V` and
`Fil^b V = 0`. Then `t_H(V) = a · dim_K V + ∑_{a < i < b} dim_K Fil^i V`. -/
theorem hodgeNumber_eq_sum [FiniteDimensional K V] (F : DecreasingFiltration K V) {a b : ℤ}
    (hab : a ≤ b) (ha : F.Fil a = ⊤) (hb : F.Fil b = ⊥) :
    F.hodgeNumber = a * finrank K V + ∑ i ∈ Finset.Ioo a b, (finrank K (F.Fil i) : ℤ) := by
  have hsupp : Function.support (fun i : ℤ => i * (finrank K (F.gr i) : ℤ)) ⊆
      ↑(Finset.Ico a b) := by
    intro i hi
    rw [Function.mem_support, finrank_gr] at hi
    rw [Finset.coe_Ico, Set.mem_Ico]
    by_contra hcon
    apply hi
    rcases lt_or_ge i a with h | h
    · rw [F.fil_eq_top_of_le ha h.le, F.fil_eq_top_of_le ha (show i + 1 ≤ a by omega), sub_self,
        mul_zero]
    · rw [F.fil_eq_bot_of_le hb (show b ≤ i by omega),
        F.fil_eq_bot_of_le hb (show b ≤ i + 1 by omega), sub_self, mul_zero]
  have hda : (finrank K (F.Fil a) : ℤ) = finrank K V := by rw [ha, finrank_top]
  have hdb : (finrank K (F.Fil b) : ℤ) = 0 := by rw [hb, finrank_bot, Nat.cast_zero]
  have key := sum_Ico_mul_sub_add (fun i => (finrank K (F.Fil i) : ℤ)) hab
  rw [hda, hdb, mul_zero, add_zero] at key
  have hsub : ∑ i ∈ Finset.Ioo a b, (finrank K (F.Fil i) : ℤ) =
      ∑ i ∈ Finset.Ioc a b, (finrank K (F.Fil i) : ℤ) := by
    refine Finset.sum_subset Finset.Ioo_subset_Ioc_self fun i hi hi' => ?_
    rw [Finset.mem_Ioc] at hi
    rw [Finset.mem_Ioo] at hi'
    rw [show i = b by omega, hdb]
  rw [hodgeNumber, finsum_eq_sum_of_support_subset _ hsupp, hsub, ← key]
  exact Finset.sum_congr rfl fun i _ => by rw [F.finrank_gr]

/-- The Hodge number of a filtration of a zero-dimensional space `V` is `0`. -/
theorem hodgeNumber_eq_zero_of_finrank_eq_zero [FiniteDimensional K V]
    (F : DecreasingFiltration K V) (h : finrank K V = 0) : F.hodgeNumber = 0 := by
  have hbot : F.Fil 0 = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp
    ((Submodule.finrank_le (F.Fil 0)).trans h.le))
  have htop : F.Fil 0 = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hbot, finrank_bot, h])
  rw [F.hodgeNumber_eq_sum le_rfl htop hbot, h]
  simp

/-- The filtration of `V` with a single jump at `n`: `Fil^i V = V` for `i ≤ n` and
`Fil^i V = 0` for `n < i`. -/
def single (n : ℤ) : DecreasingFiltration K V where
  Fil i := if i ≤ n then ⊤ else ⊥
  antitone i j hij := by
    dsimp only
    split_ifs with hj hi hi
    · exact le_rfl
    · exact absurd (hij.trans hj) hi
    · exact bot_le
    · exact bot_le
  iInf_eq_bot := eq_bot_iff.2 (iInf_le_of_le (n + 1) (by simp))
  iSup_eq_top := eq_top_iff.2 (le_iSup_of_le n (by simp))

/-- The `i`-th step of `single n` is `⊤` if `i ≤ n` and `⊥` otherwise. -/
@[simp]
theorem single_fil (n i : ℤ) :
    (single n : DecreasingFiltration K V).Fil i = if i ≤ n then ⊤ else ⊥ :=
  rfl

/-- If `V` is finite-dimensional, then the filtration `single n` of `V` has Hodge number
`n · dim_K V`. -/
theorem hodgeNumber_single [FiniteDimensional K V] (n : ℤ) :
    (single n : DecreasingFiltration K V).hodgeNumber = n * finrank K V := by
  rw [hodgeNumber_eq_sum _ (show n ≤ n + 1 by omega) (by simp) (by simp),
    Finset.sum_eq_zero fun i hi => by rw [Finset.mem_Ioo] at hi; omega, add_zero]

/-- Fontaine–Ouyang, Definition 8.36 (1): if `dim_K V = 1` and `i` is an integer with
`Fil^i V = V` and `Fil^(i+1) V = 0`, then `t_H(V) = i`. -/
theorem hodgeNumber_of_finrank_eq_one (F : DecreasingFiltration K V) (h : finrank K V = 1)
    {i : ℤ} (hi : F.Fil i = ⊤) (hi' : F.Fil (i + 1) = ⊥) : F.hodgeNumber = i := by
  have : FiniteDimensional K V := FiniteDimensional.of_finrank_pos (by omega)
  rw [F.hodgeNumber_eq_sum (show i ≤ i + 1 by omega) hi hi', h,
    Finset.sum_eq_zero fun j hj => by rw [Finset.mem_Ioo] at hj; omega]
  simp

/-- The filtration induced on `W` by an injective linear map `f : W →ₗ[K] V`:
`Fil^i W = f⁻¹(Fil^i V)`. -/
def comap (F : DecreasingFiltration K V) (f : W →ₗ[K] V) (hf : Function.Injective f) :
    DecreasingFiltration K W where
  Fil i := (F.Fil i).comap f
  antitone _ _ hij := Submodule.comap_mono (F.antitone hij)
  iInf_eq_bot := by
    rw [← Submodule.comap_iInf, F.iInf_eq_bot, Submodule.comap_bot, LinearMap.ker_eq_bot.2 hf]
  iSup_eq_top := by
    refine eq_top_iff.2 fun w _ => ?_
    have hw : f w ∈ ⨆ i, F.Fil i := by
      rw [F.iSup_eq_top]
      exact Submodule.mem_top
    obtain ⟨i, hi⟩ := (Submodule.mem_iSup_of_directed _ F.antitone.directed_le).1 hw
    exact Submodule.mem_iSup_of_mem i hi

/-- The `i`-th step of the filtration induced along an injective linear map `f` is the preimage
`f⁻¹(Fil^i V)`. -/
@[simp]
theorem comap_fil (F : DecreasingFiltration K V) (f : W →ₗ[K] V) (hf : Function.Injective f)
    (i : ℤ) : (F.comap f hf).Fil i = (F.Fil i).comap f :=
  rfl

/-- The quotient filtration on `W` along a surjective linear map `g : V →ₗ[K] W` from a
finite-dimensional space `V`: `Fil^i W = g(Fil^i V)`. -/
def map [FiniteDimensional K V] (F : DecreasingFiltration K V) (g : V →ₗ[K] W)
    (hg : Function.Surjective g) : DecreasingFiltration K W where
  Fil i := (F.Fil i).map g
  antitone _ _ hij := Submodule.map_mono (F.antitone hij)
  iInf_eq_bot := by
    obtain ⟨b, hb⟩ := F.exists_fil_eq_bot
    refine eq_bot_iff.2 (iInf_le_of_le b ?_)
    rw [hb, Submodule.map_bot]
  iSup_eq_top := by
    rw [← Submodule.map_iSup, F.iSup_eq_top, Submodule.map_top, LinearMap.range_eq_top.2 hg]

/-- The `i`-th step of the quotient filtration along a surjective linear map `g` from a
finite-dimensional space `V` is the image `g(Fil^i V)`. -/
@[simp]
theorem map_fil [FiniteDimensional K V] (F : DecreasingFiltration K V) (g : V →ₗ[K] W)
    (hg : Function.Surjective g) (i : ℤ) : (F.map g hg).Fil i = (F.Fil i).map g :=
  rfl

/-- Inducing a filtration along an injective linear map `f : W →ₗ[K] V` and then along an
injective linear map `g : U →ₗ[K] W` gives the filtration induced along `f ∘ₗ g`. -/
theorem comap_comap (F : DecreasingFiltration K V) {f : W →ₗ[K] V} {g : U →ₗ[K] W}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    (F.comap f hf).comap g hg = F.comap (f ∘ₗ g) (hf.comp hg) :=
  ext fun i => (Submodule.comap_comp g f (F.Fil i)).symm

/-- If `V` and `W` are finite-dimensional, then taking the quotient filtration along a surjective
linear map `g : V →ₗ[K] W` and then along a surjective linear map `g' : W →ₗ[K] U` gives the
quotient filtration along `g' ∘ₗ g`. -/
theorem map_map [FiniteDimensional K V] [FiniteDimensional K W] (F : DecreasingFiltration K V)
    {g : V →ₗ[K] W} {g' : W →ₗ[K] U} (hg : Function.Surjective g)
    (hg' : Function.Surjective g') :
    (F.map g hg).map g' hg' = F.map (g' ∘ₗ g) (hg'.comp hg) :=
  ext fun i => (Submodule.map_comp g g' (F.Fil i)).symm

/-- Let `V` be finite-dimensional, and let `f : V' →ₗ[K] V` be injective and `g : V →ₗ[K] V''`
satisfy `Function.Exact f g`, so that `0 → V' → V → V''` is exact. Then
`dim_K Fil^i V = dim_K f⁻¹(Fil^i V) + dim_K g(Fil^i V)` for every `i : ℤ`. -/
theorem finrank_fil_eq_add_of_exact [FiniteDimensional K V] (F : DecreasingFiltration K V)
    {f : V' →ₗ[K] V} {g : V →ₗ[K] V''} (hf : Function.Injective f)
    (hfg : Function.Exact f g) (i : ℤ) :
    finrank K (F.Fil i) = finrank K ((F.Fil i).comap f) + finrank K ((F.Fil i).map g) := by
  have h₁ := LinearMap.finrank_range_add_finrank_ker (g.domRestrict (F.Fil i))
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h₁
  have h₂ : finrank K ((LinearMap.ker g).comap (F.Fil i).subtype) =
      finrank K ((F.Fil i).comap f) := by
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, hfg.linearMap_ker_eq,
      inf_comm, ← Submodule.map_comap_eq]
    exact (Submodule.equivMapOfInjective f hf _).finrank_eq.symm
  omega

/-- Fontaine–Ouyang, Proposition 8.38 (1): let `V` be finite-dimensional, let `f : V' →ₗ[K] V`
be injective and `g : V →ₗ[K] V''` surjective with `Function.Exact f g`, so that
`0 → V' → V → V'' → 0` is exact. Giving `V'` the filtration induced along `f` and `V''` the
quotient filtration along `g`, the Hodge numbers satisfy `t_H(V) = t_H(V') + t_H(V'')`. -/
theorem hodgeNumber_eq_add_of_exact [FiniteDimensional K V] (F : DecreasingFiltration K V)
    {f : V' →ₗ[K] V} {g : V →ₗ[K] V''} (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    F.hodgeNumber = (F.comap f hf).hodgeNumber + (F.map g hg).hodgeNumber := by
  have : FiniteDimensional K V' := Module.Finite.of_injective f hf
  have : FiniteDimensional K V'' := Module.Finite.of_surjective g hg
  obtain ⟨a, b, hab, ha, hb⟩ := F.exists_le_and_fil_eq_top_and_fil_eq_bot
  have ha' : (F.comap f hf).Fil a = ⊤ := by rw [comap_fil, ha, Submodule.comap_top]
  have hb' : (F.comap f hf).Fil b = ⊥ := by
    rw [comap_fil, hb, Submodule.comap_bot, LinearMap.ker_eq_bot.2 hf]
  have ha'' : (F.map g hg).Fil a = ⊤ := by
    rw [map_fil, ha, Submodule.map_top, LinearMap.range_eq_top.2 hg]
  have hb'' : (F.map g hg).Fil b = ⊥ := by rw [map_fil, hb, Submodule.map_bot]
  rw [F.hodgeNumber_eq_sum hab ha hb, (F.comap f hf).hodgeNumber_eq_sum hab ha' hb',
    (F.map g hg).hodgeNumber_eq_sum hab ha'' hb'']
  have hV : finrank K V = finrank K V' + finrank K V'' := by
    have := F.finrank_fil_eq_add_of_exact hf hfg a
    rwa [ha, Submodule.comap_top, Submodule.map_top, LinearMap.range_eq_top.2 hg, finrank_top,
      finrank_top, finrank_top] at this
  have hsum : ∑ i ∈ Finset.Ioo a b, (finrank K (F.Fil i) : ℤ) =
      ∑ i ∈ Finset.Ioo a b, ((finrank K ((F.comap f hf).Fil i) : ℤ) +
        finrank K ((F.map g hg).Fil i)) :=
    Finset.sum_congr rfl fun i _ => by
      rw [comap_fil, map_fil, F.finrank_fil_eq_add_of_exact hf hfg i, Nat.cast_add]
  rw [hsum, Finset.sum_add_distrib, hV, Nat.cast_add]
  ring

/-- If `F` and `G` are filtrations of a finite-dimensional space `V` with `F.Fil i ≤ G.Fil i`
for every `i : ℤ`, then `t_H(F) ≤ t_H(G)`. -/
theorem hodgeNumber_le_of_le [FiniteDimensional K V] {F G : DecreasingFiltration K V}
    (h : ∀ i, F.Fil i ≤ G.Fil i) : F.hodgeNumber ≤ G.hodgeNumber := by
  obtain ⟨a, haF⟩ := F.exists_fil_eq_top
  obtain ⟨b, hbG⟩ := G.exists_fil_eq_bot
  have ha : F.Fil (min a b) = ⊤ := F.fil_eq_top_of_le haF (min_le_left a b)
  have hb : F.Fil b = ⊥ := bot_unique ((h b).trans_eq hbG)
  have ha' : G.Fil (min a b) = ⊤ := top_unique (ha.symm.trans_le (h _))
  rw [F.hodgeNumber_eq_sum (min_le_right a b) ha hb,
    G.hodgeNumber_eq_sum (min_le_right a b) ha' hbG]
  gcongr with i
  exact Submodule.finrank_mono (h i)

/-- If `F` and `G` are filtrations of a finite-dimensional space `V` with `F.Fil i ≤ G.Fil i`
for every `i : ℤ` and `t_H(G) ≤ t_H(F)`, then `F = G`. -/
theorem eq_of_le_of_hodgeNumber_le [FiniteDimensional K V] {F G : DecreasingFiltration K V}
    (h : ∀ i, F.Fil i ≤ G.Fil i) (h' : G.hodgeNumber ≤ F.hodgeNumber) : F = G := by
  obtain ⟨a, haF⟩ := F.exists_fil_eq_top
  obtain ⟨b, hbG⟩ := G.exists_fil_eq_bot
  have ha : F.Fil (min a b) = ⊤ := F.fil_eq_top_of_le haF (min_le_left a b)
  have hb : F.Fil b = ⊥ := bot_unique ((h b).trans_eq hbG)
  have ha' : G.Fil (min a b) = ⊤ := top_unique (ha.symm.trans_le (h _))
  rw [F.hodgeNumber_eq_sum (min_le_right a b) ha hb,
    G.hodgeNumber_eq_sum (min_le_right a b) ha' hbG, add_le_add_iff_left] at h'
  have hle : ∀ i ∈ Finset.Ioo (min a b) b,
      (finrank K (F.Fil i) : ℤ) ≤ finrank K (G.Fil i) :=
    fun i _ => by exact_mod_cast Submodule.finrank_mono (h i)
  have heq := (Finset.sum_eq_sum_iff_of_le hle).1 (le_antisymm (Finset.sum_le_sum hle) h')
  refine ext fun i => ?_
  rcases le_or_gt i (min a b) with hi | hi
  · rw [F.fil_eq_top_of_le ha hi, G.fil_eq_top_of_le ha' hi]
  rcases le_or_gt b i with hi' | hi'
  · rw [F.fil_eq_bot_of_le hb hi', G.fil_eq_bot_of_le hbG hi']
  refine Submodule.eq_of_le_of_finrank_le (h i) ?_
  exact_mod_cast (heq i (Finset.mem_Ioo.2 ⟨hi, hi'⟩)).ge

/-- If `V` is finite-dimensional and `e : W ≃ₗ[K] V` is a linear equivalence, then the filtration
induced on `W` along `e` has the same Hodge number as the filtration of `V`. -/
theorem hodgeNumber_comap_linearEquiv [FiniteDimensional K V] (F : DecreasingFiltration K V)
    (e : W ≃ₗ[K] V) : (F.comap (e : W →ₗ[K] V) e.injective).hodgeNumber = F.hodgeNumber := by
  have : FiniteDimensional K W := Module.Finite.equiv e.symm
  obtain ⟨a, b, hab, ha, hb⟩ := F.exists_le_and_fil_eq_top_and_fil_eq_bot
  have ha' : (F.comap (e : W →ₗ[K] V) e.injective).Fil a = ⊤ := by
    rw [comap_fil, ha, Submodule.comap_top]
  have hb' : (F.comap (e : W →ₗ[K] V) e.injective).Fil b = ⊥ := by
    rw [comap_fil, hb, Submodule.comap_bot, LinearMap.ker_eq_bot.2 e.injective]
  rw [F.hodgeNumber_eq_sum hab ha hb, (F.comap _ e.injective).hodgeNumber_eq_sum hab ha' hb',
    e.finrank_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [comap_fil, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]

/-- Induced and quotient filtrations commute across a commutative square. Let `V` and `W` be
finite-dimensional, let `j : W →ₗ[K] V` and `j' : W'' →ₗ[K] V''` be injective and
`q : V →ₗ[K] V''` and `q' : W →ₗ[K] W''` surjective, with `q ∘ₗ j = j' ∘ₗ q'` and
`ker q ≤ range j`. Then the filtration induced along `j'` by the quotient filtration along `q`
equals the quotient filtration along `q'` of the filtration induced along `j`. -/
theorem comap_map_eq_map_comap [FiniteDimensional K V] [FiniteDimensional K W]
    (F : DecreasingFiltration K V) {j : W →ₗ[K] V} {q : V →ₗ[K] V''} {j' : W'' →ₗ[K] V''}
    {q' : W →ₗ[K] W''} (hj : Function.Injective j) (hq : Function.Surjective q)
    (hj' : Function.Injective j') (hq' : Function.Surjective q') (hcomm : q ∘ₗ j = j' ∘ₗ q')
    (hker : LinearMap.ker q ≤ LinearMap.range j) :
    (F.map q hq).comap j' hj' = (F.comap j hj).map q' hq' := by
  have hc : ∀ w, q (j w) = j' (q' w) := fun w => LinearMap.congr_fun hcomm w
  refine ext fun i => le_antisymm ?_ ?_
  · intro x hx
    rw [comap_fil, Submodule.mem_comap, map_fil, Submodule.mem_map] at hx
    obtain ⟨v, hv, hvx⟩ := hx
    obtain ⟨w, rfl⟩ := hq' x
    obtain ⟨u, hu⟩ := hker (show v - j w ∈ LinearMap.ker q by
      rw [LinearMap.mem_ker, map_sub, hvx, hc, sub_self])
    have hqu : q' u = 0 := hj' (by rw [map_zero, ← hc, hu, map_sub, hvx, hc, sub_self])
    rw [map_fil, comap_fil, Submodule.mem_map]
    refine ⟨w + u, ?_, by rw [map_add, hqu, add_zero]⟩
    rw [Submodule.mem_comap, map_add, hu, add_sub_cancel]
    exact hv
  · rintro _ ⟨w, hw, rfl⟩
    rw [comap_fil, Submodule.mem_comap, map_fil, ← hc]
    exact Submodule.mem_map_of_mem hw

end DecreasingFiltration
