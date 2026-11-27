/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Ramification
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The finite places of a finite extension and the size of an element

Let `L'/L` be a finite extension of number fields. For a finite place `v` of `L` (a maximal ideal
`𝔭_v` of `𝓞 L`, a `HeightOneSpectrum`) let `‖x‖_v = Nv ^ (-ord_v x)` with `Nv = #(𝓞 L / 𝔭_v)`
and `‖0‖_v = 0`; this is Mathlib's `NumberField.HeightOneSpectrum.adicAbv L v`. For every
`x ∈ L`,

* `∑_{w ∣ v} log max(1, ‖x‖_w) = [L' : L] log max(1, ‖x‖_v)`, the sum over the finite places
  `w` of `L'` above `v` (`NumberField.sum_log_max_one_adicAbv_liesOver`);
* `∑_w log max(1, ‖x‖_w) = [L' : L] ∑_v log max(1, ‖x‖_v)`, over all finite places
  (`NumberField.finsum_log_max_one_adicAbv`).

The proof combines Mathlib's comparison of valuations along the extension
(`IsDedekindDomain.HeightOneSpectrum.valuation_liesOver`, `w(x) = e(w ∣ v) v(x)`), the norm
identity `Nw = Nv ^ f(w ∣ v)` (`Ideal.absNorm_pow_inertiaDeg`) and the degree formula
`∑_{w ∣ v} e(w ∣ v) f(w ∣ v) = [L' : L]` (`Ideal.sum_ramification_inertia_eq_finrank`).
-/

@[expose] public section

open IsDedekindDomain NumberField Real

namespace NumberField

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- `log max(1, a^n) = n log max(1, a)` for a real `a ≥ 0`. -/
theorem log_max_one_pow {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    log (max 1 (a ^ n)) = n * log (max 1 a) := by
  rw [← Real.log_pow]
  congr 1
  rcases le_total a 1 with h | h
  · rw [max_eq_left h, one_pow, max_eq_left (pow_le_one₀ ha h)]
  · rw [max_eq_right h, max_eq_right (one_le_pow₀ h)]

/-- The finite place of `K` below a finite place `w` of `L`: the prime `𝔭_w ∩ 𝓞 K`. -/
noncomputable def HeightOneSpectrum.under (w : HeightOneSpectrum (𝓞 L)) :
    HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := Ideal.IsMaximal.ne_bot_of_isIntegral_int _

instance (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.LiesOver (HeightOneSpectrum.under K L w).asIdeal :=
  ⟨rfl⟩

theorem HeightOneSpectrum.eq_under {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    (h : w.asIdeal.LiesOver v.asIdeal) : v = HeightOneSpectrum.under K L w :=
  HeightOneSpectrum.ext h.over

/-- **The absolute value of an element at a place above.** Let `L/K` be an extension of number
fields, `v` a finite place of `K` and `w` a finite place of `L` above `v`, with ramification index
`e(w ∣ v)` and inertia degree `f(w ∣ v)`. Then for every `x ∈ K`,
`‖x‖_w = ‖x‖_v ^ (e(w ∣ v) f(w ∣ v))`, where `‖x‖_v = Nv ^ (-ord_v x)`
(`NumberField.HeightOneSpectrum.adicAbv`). -/
theorem adicAbv_algebraMap_liesOver (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] (x : K) :
    HeightOneSpectrum.adicAbv L w (algebraMap K L x) =
      HeightOneSpectrum.adicAbv K v x ^
        (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)) := by
  have he : 0 < w.asIdeal.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx_pos_of_isDedekindDomain' w.asIdeal v.ne_bot
  have hf : 0 < w.asIdeal.inertiaDeg (𝓞 K) := Ideal.inertiaDeg_pos w.asIdeal (𝓞 K)
  rw [HeightOneSpectrum.adicAbv_def, HeightOneSpectrum.adicAbv_def,
    ← HeightOneSpectrum.valuation_liesOver L v w x]
  have hN : (Ideal.absNorm w.asIdeal : NNReal) =
      (Ideal.absNorm v.asIdeal : NNReal) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
    rw [← Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal]
    push_cast
    rfl
  rcases eq_or_ne (HeightOneSpectrum.valuation K v x) 0 with h0 | h0
  · rw [h0, zero_pow he.ne', map_zero, map_zero, NNReal.coe_zero, zero_pow (by positivity)]
  · rw [WithZeroMulInt.toNNReal_neg_apply _ (pow_ne_zero _ h0),
      WithZeroMulInt.toNNReal_neg_apply _ h0, WithZero.log_pow, hN, NNReal.coe_zpow,
      NNReal.coe_zpow, NNReal.coe_pow, ← zpow_natCast (_ : ℝ) (w.asIdeal.inertiaDeg (𝓞 K)),
      ← zpow_mul, ← zpow_natCast (_ : ℝ) (_ * _), ← zpow_mul]
    congr 1
    rw [nsmul_eq_mul]
    push_cast
    ring

/-- `log max(1, ‖x‖_w) = e(w ∣ v) f(w ∣ v) log max(1, ‖x‖_v)` for a finite place `w` of `L`
above a finite place `v` of `K` and `x ∈ K`. -/
theorem log_max_one_adicAbv_algebraMap_liesOver (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] (x : K) :
    log (max 1 (HeightOneSpectrum.adicAbv L w (algebraMap K L x))) =
      (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) : ℕ) *
        log (max 1 (HeightOneSpectrum.adicAbv K v x)) := by
  rw [adicAbv_algebraMap_liesOver K L v w x, log_max_one_pow (AbsoluteValue.nonneg _ _)]

theorem finrank_ringOfIntegers : Module.finrank (𝓞 K) (𝓞 L) = Module.finrank K L := by
  unfold Module.finrank
  rw [← Algebra.IsAlgebraic.rank_of_isFractionRing (𝓞 K) K (𝓞 L) L]

/-- The finite places of `L` above `v`, as a subtype of `HeightOneSpectrum (𝓞 L)`, are the prime
ideals of `𝓞 L` over `𝔭_v`. -/
noncomputable def liesOverEquivPrimesOver (v : HeightOneSpectrum (𝓞 K)) :
    {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal} ≃
      v.asIdeal.primesOver (𝓞 L) where
  toFun w := ⟨w.1.asIdeal, w.1.isPrime, w.2⟩
  invFun q := ⟨⟨q.1, q.2.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot q.1⟩,
    q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem finite_setOf_liesOver (v : HeightOneSpectrum (𝓞 K)) :
    {w : HeightOneSpectrum (𝓞 L) | w.asIdeal.LiesOver v.asIdeal}.Finite :=
  Set.finite_coe_iff.mp (Finite.of_equiv _ (liesOverEquivPrimesOver K L v).symm)

/-- **The finite places of a finite extension and the size of an element**, at one place. Let
`L/K` be a finite extension of number fields (the page's `L'/L`), `v` a finite place of `K` and
`x ∈ K`. Then
`∑_{w ∣ v} log max(1, ‖x‖_w) = [L : K] log max(1, ‖x‖_v)`,
the sum running over the finite places `w` of `L` above `v` (those with
`𝔭_w ∩ 𝓞 K = 𝔭_v`), where `‖x‖_v = Nv ^ (-ord_v x)`, `‖0‖_v = 0`
(`NumberField.HeightOneSpectrum.adicAbv`).

The normalization of `‖·‖_v` is that of P. Deligne, "Preuve des conjectures de Tate et de
Shafarevitch [d'après G. Faltings]", Séminaire Bourbaki, exposé 616, Astérisque 121–122 (1985),
25–41, §1.1, p. 26. The identity is proved here from `w(x) = e(w ∣ v) v(x)`, `Nw = Nv ^ f(w ∣ v)`
and `∑_{w ∣ v} e(w ∣ v) f(w ∣ v) = [L : K]`. -/
theorem sum_log_max_one_adicAbv_liesOver (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    ∑ᶠ (w : HeightOneSpectrum (𝓞 L)) (_ : w.asIdeal.LiesOver v.asIdeal),
        log (max 1 (HeightOneSpectrum.adicAbv L w (algebraMap K L x))) =
      Module.finrank K L * log (max 1 (HeightOneSpectrum.adicAbv K v x)) := by
  classical
  let := Fintype.ofFinite (v.asIdeal.primesOver (𝓞 L))
  rw [← finsum_subtype_eq_finsum_cond (fun w : HeightOneSpectrum (𝓞 L) ↦
      w.asIdeal.LiesOver v.asIdeal),
    ← finsum_comp_equiv (liesOverEquivPrimesOver K L v).symm, finsum_eq_sum_of_fintype]
  have key : ∀ q : v.asIdeal.primesOver (𝓞 L),
      log (max 1 (HeightOneSpectrum.adicAbv L ((liesOverEquivPrimesOver K L v).symm q).1
        (algebraMap K L x))) =
      (q.1.ramificationIdx (𝓞 K) * q.1.inertiaDeg (𝓞 K) : ℕ) *
        log (max 1 (HeightOneSpectrum.adicAbv K v x)) := by
    intro q
    have : ((liesOverEquivPrimesOver K L v).symm q).1.asIdeal.LiesOver v.asIdeal :=
      ((liesOverEquivPrimesOver K L v).symm q).2
    exact log_max_one_adicAbv_algebraMap_liesOver K L v _ x
  simp_rw [key]
  rw [← Finset.sum_mul, ← Nat.cast_sum, Ideal.sum_ramification_inertia_eq_finrank,
    finrank_ringOfIntegers]

private theorem finsum_mem_eq_finsum_of_support_subset' {α : Type*} (f : α → ℝ) {s : Set α}
    (h : Function.support f ⊆ s) : ∑ᶠ i ∈ s, f i = ∑ᶠ i, f i := by
  rw [← finsum_mem_inter_support, Set.inter_eq_right.mpr h, finsum_mem_support]

/-- **The finite places of a finite extension and the size of an element**, summed over all
places. Let `L/K` be a finite extension of number fields and `x ∈ K`. Then
`∑_w log max(1, ‖x‖_w) = [L : K] ∑_v log max(1, ‖x‖_v)`,
the sums running over all finite places `w` of `L` and `v` of `K` (as finite sums: only finitely
many terms are nonzero), with `‖x‖_v = Nv ^ (-ord_v x)`, `‖0‖_v = 0`
(`NumberField.HeightOneSpectrum.adicAbv`).

The normalization of `‖·‖_v` is that of P. Deligne, Séminaire Bourbaki, exposé 616, Astérisque
121–122 (1985), §1.1, p. 26. The identity is proved here: each finite place of `L` lies above
exactly one finite place of `K`, and `NumberField.sum_log_max_one_adicAbv_liesOver` sums the
places above each. -/
theorem finsum_log_max_one_adicAbv (x : K) :
    ∑ᶠ w : HeightOneSpectrum (𝓞 L),
        log (max 1 (HeightOneSpectrum.adicAbv L w (algebraMap K L x))) =
      Module.finrank K L *
        ∑ᶠ v : HeightOneSpectrum (𝓞 K), log (max 1 (HeightOneSpectrum.adicAbv K v x)) := by
  set h : HeightOneSpectrum (𝓞 K) → ℝ := fun v ↦ log (max 1 (HeightOneSpectrum.adicAbv K v x))
  set g : HeightOneSpectrum (𝓞 L) → ℝ :=
    fun w ↦ log (max 1 (HeightOneSpectrum.adicAbv L w (algebraMap K L x)))
  set O : HeightOneSpectrum (𝓞 K) → Set (HeightOneSpectrum (𝓞 L)) :=
    fun v ↦ {w | w.asIdeal.LiesOver v.asIdeal}
  -- `h v ≠ 0` only when `‖x‖_v > 1`, that is, at finitely many places.
  have hsupp : (Function.support h).Finite := by
    refine (HeightOneSpectrum.Support.finite (𝓞 K) x).subset fun v hv ↦ ?_
    by_contra hle
    apply hv
    simp only [HeightOneSpectrum.Support, Set.mem_ofPred_eq, not_lt] at hle
    have : HeightOneSpectrum.adicAbv K v x ≤ 1 := by
      rw [HeightOneSpectrum.adicAbv_def]
      exact_mod_cast (WithZeroMulInt.toNNReal_le_one_iff
        (HeightOneSpectrum.one_lt_absNorm_nnreal v)).mpr hle
    simp [h, max_eq_left this]
  have hg : ∀ w, g w =
      (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) : ℕ) *
        h (HeightOneSpectrum.under K L w) :=
    fun w ↦ log_max_one_adicAbv_algebraMap_liesOver K L _ w x
  have hsub : Function.support g ⊆ ⋃ v ∈ Function.support h, O v := by
    intro w hw
    refine Set.mem_biUnion (x := HeightOneSpectrum.under K L w) ?_ (show w.asIdeal.LiesOver _
      from inferInstance)
    intro h0
    exact hw (by rw [hg w, h0, mul_zero])
  have hdisj : (Function.support h).PairwiseDisjoint O := by
    intro v₁ _ v₂ _ hne
    refine Set.disjoint_left.mpr fun w h₁ h₂ ↦ hne ?_
    rw [HeightOneSpectrum.eq_under K L h₁, HeightOneSpectrum.eq_under K L h₂]
  rw [← finsum_mem_eq_finsum_of_support_subset' g hsub, finsum_mem_biUnion hdisj hsupp
      fun v _ ↦ finite_setOf_liesOver K L v, ← finsum_mem_eq_finsum_of_support_subset' h
      subset_rfl, mul_finsum_mem]
  refine finsum_mem_congr rfl fun v _ ↦ ?_
  exact sum_log_max_one_adicAbv_liesOver K L v x

end NumberField
