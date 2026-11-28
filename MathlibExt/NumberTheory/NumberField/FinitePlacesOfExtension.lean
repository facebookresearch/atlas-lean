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
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import MathlibExt.NumberTheory.NumberField.Completion.FinitePlacesOver

/-!
# The finite places of a finite extension and the size of an element

Let `L/K` be a finite extension of number fields. For a finite place `v` of `K` (a maximal ideal
`𝔭_v` of `𝓞 K`, a `HeightOneSpectrum`) let `‖x‖_v = Nv ^ (-ord_v x)` with `Nv = #(𝓞 K / 𝔭_v)`
and `‖0‖_v = 0`; this is Mathlib's `NumberField.HeightOneSpectrum.adicAbv K v`. For every
`x ∈ K`,

* `∑_{w ∣ v} log max(1, ‖x‖_w) = [L : K] log max(1, ‖x‖_v)`, the sum over the finite places
  `w` of `L` above `v` (`NumberField.sum_log_max_one_adicAbv_liesOver`);
* `∑_w log max(1, ‖x‖_w) = [L : K] ∑_v log max(1, ‖x‖_v)`, over all finite places
  (`NumberField.finsum_log_max_one_adicAbv`).

The proof combines Mathlib's comparison of absolute values along the extension
(`NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply_algebraMap`,
`‖x‖_w = ‖x‖_v ^ (e(w ∣ v) f(w ∣ v))`, which rests on `w(x) = e(w ∣ v) v(x)` and
`Nw = Nv ^ f(w ∣ v)`) with the degree formula `∑_{w ∣ v} e(w ∣ v) f(w ∣ v) = [L : K]`
(`Ideal.sum_ramification_inertia_eq_finrank`, with `IsFractionRing.finrank_eq`), indexing the
places above `v` by `IsDedekindDomain.HeightOneSpectrum.placesOver`.
-/

@[expose] public section

open IsDedekindDomain NumberField Real

namespace NumberField

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- `log max(1, ‖x‖_w) = e(w ∣ v) f(w ∣ v) log max(1, ‖x‖_v)` for a finite place `w` of `L`
above a finite place `v` of `K` and `x ∈ K`. -/
theorem log_max_one_adicAbv_algebraMap_liesOver (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] (x : K) :
    log (max 1 (HeightOneSpectrum.adicAbv L w (algebraMap K L x))) =
      (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) : ℕ) *
        log (max 1 (HeightOneSpectrum.adicAbv K v x)) := by
  have h := FinitePlace.equivHeightOneSpectrum_symm_apply_algebraMap v w x
  rw [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.equivHeightOneSpectrum_symm_apply,
    FinitePlace.norm_embedding, FinitePlace.norm_embedding] at h
  rw [h, ← Real.posLog_eq_log_max_one (pow_nonneg (AbsoluteValue.nonneg _ _) _),
    ← Real.posLog_eq_log_max_one (AbsoluteValue.nonneg _ _), Real.posLog_pow]

/-- **The finite places of a finite extension and the size of an element**, at one place. Let
`L/K` be a finite extension of number fields, `v` a finite place of `K` and
`x ∈ K`. Then
`∑_{w ∣ v} log max(1, ‖x‖_w) = [L : K] log max(1, ‖x‖_v)`,
the sum running over the finite places `w` of `L` above `v` (those with
`𝔭_w ∩ 𝓞 K = 𝔭_v`), where `‖x‖_v = Nv ^ (-ord_v x)`, `‖0‖_v = 0`
(`NumberField.HeightOneSpectrum.adicAbv`).

The normalization of `‖·‖_v` is that of P. Deligne, "Preuve des conjectures de Tate et de
Shafarevitch [d'après G. Faltings]", Séminaire Bourbaki, exposé 616, Astérisque 121–122 (1985),
25–41, §1.1, p. 26. The identity follows from `w(x) = e(w ∣ v) v(x)`, `Nw = Nv ^ f(w ∣ v)` and
`∑_{w ∣ v} e(w ∣ v) f(w ∣ v) = [L : K]`. -/
theorem sum_log_max_one_adicAbv_liesOver (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    ∑ᶠ (w : HeightOneSpectrum (𝓞 L)) (_ : w.asIdeal.LiesOver v.asIdeal),
        log (max 1 (HeightOneSpectrum.adicAbv L w (algebraMap K L x))) =
      Module.finrank K L * log (max 1 (HeightOneSpectrum.adicAbv K v x)) := by
  classical
  let := Fintype.ofFinite (v.asIdeal.primesOver (𝓞 L))
  rw [← finsum_subtype_eq_finsum_cond (fun w : HeightOneSpectrum (𝓞 L) ↦
      w.asIdeal.LiesOver v.asIdeal)]
  change ∑ᶠ w : v.placesOver L, _ = _
  rw [← finsum_comp_equiv (v.placesOverEquivPrimesOver L).symm, finsum_eq_sum_of_fintype]
  have key : ∀ q : v.asIdeal.primesOver (𝓞 L),
      log (max 1 (HeightOneSpectrum.adicAbv L ((v.placesOverEquivPrimesOver L).symm q).1
        (algebraMap K L x))) =
      (q.1.ramificationIdx (𝓞 K) * q.1.inertiaDeg (𝓞 K) : ℕ) *
        log (max 1 (HeightOneSpectrum.adicAbv K v x)) := by
    intro q
    have : ((v.placesOverEquivPrimesOver L).symm q).1.asIdeal.LiesOver v.asIdeal :=
      ((v.placesOverEquivPrimesOver L).symm q).2
    exact log_max_one_adicAbv_algebraMap_liesOver K L v _ x
  simp_rw [key]
  rw [← Finset.sum_mul, ← Nat.cast_sum, Ideal.sum_ramification_inertia_eq_finrank,
    ← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L]

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
121–122 (1985), §1.1, p. 26. Each finite place of `L` lies above exactly one finite place of `K`,
and `NumberField.sum_log_max_one_adicAbv_liesOver` sums the places above each. -/
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
  -- each `w` lies over the place `under (𝓞 K) w` below it, and only over it.
  have hover : ∀ w : HeightOneSpectrum (𝓞 L),
      w.asIdeal.LiesOver (HeightOneSpectrum.under (𝓞 K) w).asIdeal := fun w ↦ by
    rw [HeightOneSpectrum.under_asIdeal]
    exact Ideal.over_under _
  have heq : ∀ {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)},
      w.asIdeal.LiesOver v.asIdeal → v = HeightOneSpectrum.under (𝓞 K) w := fun hvw ↦
    HeightOneSpectrum.ext (by rw [HeightOneSpectrum.under_asIdeal]; exact hvw.over)
  have hg : ∀ w, g w =
      (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) : ℕ) *
        h (HeightOneSpectrum.under (𝓞 K) w) := fun w ↦ by
    have := hover w
    exact log_max_one_adicAbv_algebraMap_liesOver K L _ w x
  have hsub : Function.support g ⊆ ⋃ v ∈ Function.support h, O v := by
    intro w hw
    refine Set.mem_biUnion (x := HeightOneSpectrum.under (𝓞 K) w) ?_ (hover w)
    intro h0
    exact hw (by rw [hg w, h0, mul_zero])
  have hdisj : (Function.support h).PairwiseDisjoint O := by
    intro v₁ _ v₂ _ hne
    refine Set.disjoint_left.mpr fun w h₁ h₂ ↦ hne ?_
    rw [heq h₁, heq h₂]
  rw [← finsum_mem_eq_finsum_of_support_subset' g hsub, finsum_mem_biUnion hdisj hsupp
      fun v _ ↦ @Set.toFinite _ (O v) (inferInstance : Finite (v.placesOver L)),
    ← finsum_mem_eq_finsum_of_support_subset' h
      subset_rfl, mul_finsum_mem]
  refine finsum_mem_congr rfl fun v _ ↦ ?_
  exact sum_log_max_one_adicAbv_liesOver K L v x

end NumberField
