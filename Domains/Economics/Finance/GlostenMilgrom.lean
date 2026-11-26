/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Martingale.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The sequential Glosten–Milgrom market

`Sample` records the value bit and a stream of pairs (informed bit, noise-order bit).
`law` makes these independent with Bernoulli marginals. `order` observes only the
trade, with `true` meaning buy and `false` meaning sell. Period `n` in Lean is
period `n + 1` in the model. `history n` records the first `n` orders and
`orderFiltration n` is the σ-algebra they generate. `atom h` is the event that
this observed prefix is `h`.

`jointWeight` is the explicit prior times likelihood. `posterior` normalizes the
high-value weight by the total, `prefixPrice` is the corresponding mean, and
`quote` is the mean after appending a specified buy or sell. `transactionPrice`
is the mean after the trades observed so far (the prior mean at time zero).
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory unitInterval

namespace MathlibExt.Probability.Finance.GlostenMilgrom

public section

abbrev Sample := Bool × (ℕ → Bool × Bool)

@[expose] noncomputable def fair : I := ⟨1 / 2, by constructor <;> norm_num⟩

@[expose] noncomputable def periodLaw (μ : I) : Measure (Bool × Bool) :=
  (bernoulliMeasure true false μ).prod (bernoulliMeasure true false fair)

@[expose] noncomputable def law (p μ : I) : Measure Sample :=
  (bernoulliMeasure true false p).prod (Measure.infinitePi fun _ : ℕ ↦ periodLaw μ)

@[expose] def valueEvent (v : Bool) : Set Sample := {ω | ω.1 = v}

@[expose] def value (low high : ℝ) (ω : Sample) : ℝ := if ω.1 then high else low

@[expose] def orderOf (v : Bool) (bits : Bool × Bool) : Bool :=
  if bits.1 then v else bits.2

@[expose] def order (n : ℕ) (ω : Sample) : Bool := orderOf ω.1 (ω.2 n)

@[expose] def history (n : ℕ) (ω : Sample) (i : Fin n) : Bool := order i ω

@[expose] def atom {n : ℕ} (h : Fin n → Bool) : Set Sample := history n ⁻¹' {h}

@[expose] def orderFiltration : Filtration ℕ (inferInstance : MeasurableSpace Sample) where
  seq n := MeasurableSpace.comap (history n) inferInstance
  mono' := by
    intro i j hij
    let cut : (Fin j → Bool) → (Fin i → Bool) := fun h k ↦ h (Fin.castLE hij k)
    change MeasurableSpace.comap (cut ∘ history j) inferInstance ≤ _
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (Measurable.of_discrete (f := cut)).comap_le
  le' n := (measurable_pi_iff.2 fun i ↦
    (Measurable.of_discrete (f := fun a : Bool × (Bool × Bool) ↦ orderOf a.1 a.2)).comp
      (measurable_fst.prodMk ((measurable_pi_apply i.val).comp measurable_snd))).comap_le

@[expose] noncomputable def likelihood (μ : I) (v d : Bool) : ℝ :=
  if v = d then (1 + (μ : ℝ)) / 2 else (1 - (μ : ℝ)) / 2

@[expose] noncomputable def jointWeight (p μ : I) {n : ℕ} (h : Fin n → Bool) (v : Bool) : ℝ :=
  (if v then (p : ℝ) else 1 - (p : ℝ)) * ∏ i, likelihood μ v (h i)

@[expose] noncomputable def posterior (p μ : I) {n : ℕ} (h : Fin n → Bool) : ℝ :=
  jointWeight p μ h true / (jointWeight p μ h true + jointWeight p μ h false)

@[expose] noncomputable def prefixPrice (p μ : I) (low high : ℝ) {n : ℕ}
    (h : Fin n → Bool) : ℝ :=
  low + (high - low) * posterior p μ h

@[expose] noncomputable def quote (p μ : I) (low high : ℝ) {n : ℕ}
    (h : Fin n → Bool) (d : Bool) : ℝ := prefixPrice p μ low high (Fin.snoc h d)

@[expose] noncomputable def transactionPrice (p μ : I) (low high : ℝ) (n : ℕ) (ω : Sample) : ℝ :=
  prefixPrice p μ low high (history n ω)

end

private instance (μ : I) : IsProbabilityMeasure (periodLaw μ) := by
  unfold periodLaw
  infer_instance

private instance (p μ : I) : IsProbabilityMeasure (law p μ) := by
  unfold law
  infer_instance

private theorem measurable_order (n : ℕ) : Measurable (order n) :=
  (Measurable.of_discrete (f := fun a : Bool × (Bool × Bool) ↦ orderOf a.1 a.2)).comp
    (measurable_fst.prodMk ((measurable_pi_apply n).comp measurable_snd))

private theorem measurable_history (n : ℕ) : Measurable (history n) :=
  measurable_pi_iff.2 fun i ↦ measurable_order i

private theorem measurable_atom {n : ℕ} (h : Fin n → Bool) : MeasurableSet (atom h) :=
  measurable_history n (measurableSet_singleton h)

private theorem measurable_valueEvent (v : Bool) : MeasurableSet (valueEvent v) :=
  measurable_fst (measurableSet_singleton v)

private theorem history_succ (n : ℕ) (ω : Sample) :
    history (n + 1) ω = Fin.snoc (history n ω) (order n ω) := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [history]
  · simp [history]

private theorem valueEvent_prod (v : Bool) :
    valueEvent v = {v} ×ˢ (univ : Set (ℕ → Bool × Bool)) := by
  ext ω
  simp [valueEvent]

private theorem valueEvent_mass (p μ : I) (v : Bool) :
    (law p μ).real (valueEvent v) = if v then (p : ℝ) else 1 - (p : ℝ) := by
  rw [valueEvent_prod, law, measureReal_prod_prod]
  cases v <;> simp

private theorem likelihood_pos {μ : I} (hμ : (μ : ℝ) < 1) (v d : Bool) :
    0 < likelihood μ v d := by
  have hm := μ.2.1
  unfold likelihood
  split <;> linarith

private theorem jointWeight_pos {p μ : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hμ : (μ : ℝ) < 1) {n : ℕ} (h : Fin n → Bool) (v : Bool) :
    0 < jointWeight p μ h v := by
  unfold jointWeight
  refine mul_pos ?_ (Finset.prod_pos fun i _ ↦ likelihood_pos hμ v (h i))
  cases v <;> simp [hp0, sub_pos.mpr hp1]

private theorem periodOrder_mass (μ : I) (v d : Bool) :
    (periodLaw μ).real (orderOf v ⁻¹' {d}) = likelihood μ v d := by
  classical
  let A : Set (Bool × Bool) := {true} ×ˢ (if v = d then univ else ∅)
  let B : Set (Bool × Bool) := {false} ×ˢ {d}
  have hab : Disjoint A B := by
    rw [Set.disjoint_left]
    intro a ha hb
    have ht : a.1 = true := ha.1
    have hf : a.1 = false := hb.1
    simp_all
  have heq : orderOf v ⁻¹' {d} = A ∪ B := by
    ext ⟨b, c⟩
    cases b <;> by_cases hv : v = d <;> simp [A, B, orderOf, hv]
  rw [heq, measureReal_union hab ((measurableSet_singleton false).prod (measurableSet_singleton d))]
  simp only [A, B, periodLaw, measureReal_prod_prod]
  cases v <;> cases d <;> simp [fair, likelihood] <;> ring

private theorem valueEvent_ne_zero {p μ : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (v : Bool) : law p μ (valueEvent v) ≠ 0 := by
  intro h
  have hpos : 0 < (law p μ).real (valueEvent v) := by
    rw [valueEvent_mass]
    cases v <;> simp [hp0, sub_pos.mpr hp1]
  simp [measureReal_def, h] at hpos

private theorem cond_snd {p μ : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (v : Bool) :
    ((law p μ)[|valueEvent v]).map Prod.snd = Measure.infinitePi (fun _ : ℕ ↦ periodLaw μ) := by
  refine Measure.ext fun s hs ↦ ?_
  have hrect : valueEvent v ∩ Prod.snd ⁻¹' s = {v} ×ˢ s := by
    ext ω
    simp [valueEvent]
  have hv : (bernoulliMeasure true false p) {v} ≠ 0 := by
    have h := valueEvent_ne_zero (μ := μ) hp0 hp1 v
    rwa [valueEvent_prod, law, Measure.prod_prod, measure_univ, mul_one] at h
  rw [Measure.map_apply measurable_snd hs, cond_apply (measurable_valueEvent v), hrect,
    valueEvent_prod, law, Measure.prod_prod, Measure.prod_prod, measure_univ, mul_one,
    ← mul_assoc, ENNReal.inv_mul_cancel hv (measure_ne_top _ _), one_mul]

private theorem conditional_path_law {p μ : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (v : Bool) :
    ((law p μ)[|valueEvent v]).map (fun ω n ↦ order n ω) =
      Measure.infinitePi (fun _ : ℕ ↦ (periodLaw μ).map (orderOf v)) := by
  have hv : ∀ᵐ ω ∂(law p μ)[|valueEvent v], ω ∈ valueEvent v :=
    ae_cond_mem (measurable_valueEvent v)
  have heq : (fun ω n ↦ order n ω) =ᵐ[(law p μ)[|valueEvent v]]
      (fun ω n ↦ orderOf v (ω.2 n)) := hv.mono fun ω hw ↦ by
    change ω.1 = v at hw
    funext n
    simp [order, hw]
  rw [Measure.map_congr heq]
  let f : (ℕ → Bool × Bool) → (ℕ → Bool) := fun x n ↦ orderOf v (x n)
  have hf : Measurable f := measurable_pi_iff.2 fun n ↦
    (Measurable.of_discrete (f := orderOf v)).comp (measurable_pi_apply n)
  change Measure.map (f ∘ Prod.snd) _ = _
  rw [← Measure.map_map hf measurable_snd, cond_snd hp0 hp1,
    Measure.infinitePi_map_pi _ (fun _ ↦ Measurable.of_discrete)]

private theorem conditional_order_law {p μ : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (v : Bool) (n : ℕ) :
    ((law p μ)[|valueEvent v]).map (order n) = (periodLaw μ).map (orderOf v) := by
  calc
    _ = (((law p μ)[|valueEvent v]).map (fun ω k ↦ order k ω)).map (fun x ↦ x n) := by
      rw [Measure.map_map (measurable_pi_apply n) (measurable_pi_iff.2 measurable_order)]
      rfl
    _ = _ := by rw [conditional_path_law hp0 hp1 v, Measure.infinitePi_map_eval]

private theorem conditional_orders {p μ : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (v : Bool) : iIndepFun order ((law p μ)[|valueEvent v]) ∧
      ∀ n d, ((law p μ)[|valueEvent v]).real (order n ⁻¹' {d}) = likelihood μ v d := by
  have : IsProbabilityMeasure ((law p μ)[|valueEvent v]) :=
    cond_isProbabilityMeasure (valueEvent_ne_zero hp0 hp1 v)
  constructor
  · rw [iIndepFun_iff_map_fun_eq_infinitePi_map measurable_order,
      conditional_path_law hp0 hp1 v]
    simp only [conditional_order_law hp0 hp1 v]
  · intro n d
    simp only [measureReal_def] at ⊢
    rw [← Measure.map_apply (measurable_order n) (measurableSet_singleton d),
      conditional_order_law hp0 hp1 v n,
      Measure.map_apply Measurable.of_discrete (measurableSet_singleton d)]
    exact periodOrder_mass μ v d

private theorem jointWeight_snoc (p μ : I) {n : ℕ} (h : Fin n → Bool) (v d : Bool) :
    jointWeight p μ (Fin.snoc h d) v = jointWeight p μ h v * likelihood μ v d := by
  rw [jointWeight, Fin.prod_univ_castSucc, jointWeight]
  simp [mul_assoc]

private theorem joint_mass {p μ : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {n : ℕ} (h : Fin n → Bool) (v : Bool) :
    (law p μ).real (atom h ∩ valueEvent v) = jointWeight p μ h v := by
  classical
  let K : Finset ℕ := (Finset.univ : Finset (Fin n)).map ⟨Fin.val, Fin.val_injective⟩
  let T (k : ℕ) : Set Bool := if hk : k < n then {h ⟨k, hk⟩} else univ
  have hK : MeasurableSet ((↑K : Set ℕ).pi T) :=
    MeasurableSet.pi K.countable_toSet fun _ _ ↦ MeasurableSet.of_discrete
  have hatom : atom h = (fun ω k ↦ order k ω) ⁻¹' (↑K : Set ℕ).pi T := by
    ext ω
    constructor
    · intro hw k hk
      have he : history n ω = h := hw
      rcases Finset.mem_map.mp hk with ⟨i, _, rfl⟩
      simpa [T, i.isLt, history] using congrFun he i
    · intro hw
      change history n ω = h
      funext i
      have hi : i.val ∈ K := Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
      simpa [T, i.isLt, history] using hw i.val hi
  have hmass : ((law p μ)[|valueEvent v]).real (atom h) = ∏ i, likelihood μ v (h i) := by
    rw [hatom, measureReal_def, ← Measure.map_apply (measurable_pi_iff.2 measurable_order) hK,
      conditional_path_law hp0 hp1 v,
      Measure.infinitePi_pi _ (fun _ _ ↦ MeasurableSet.of_discrete), ENNReal.toReal_prod]
    simp only [K, Finset.prod_map]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    simpa [T, i.isLt, measureReal_def, Measure.map_apply Measurable.of_discrete] using
      periodOrder_mass μ v (h i)
  have hpos : (law p μ).real (valueEvent v) ≠ 0 := by
    rw [valueEvent_mass]
    cases v <;> simp [ne_of_gt hp0, ne_of_gt (sub_pos.mpr hp1)]
  rw [measureReal_def, cond_apply (measurable_valueEvent v), ENNReal.toReal_mul,
    ENNReal.toReal_inv, ← measureReal_def, ← measureReal_def, inter_comm] at hmass
  rw [jointWeight, ← valueEvent_mass, ← hmass]
  field_simp

private theorem split_value (s : Set Sample) :
    (s ∩ valueEvent true) ∪ (s ∩ valueEvent false) = s := by
  ext ω
  cases h : ω.1 <;> simp [valueEvent, h]

private theorem disjoint_value (s : Set Sample) :
    Disjoint (s ∩ valueEvent true) (s ∩ valueEvent false) := by
  refine Set.disjoint_left.2 fun ω ht hf ↦ ?_
  have ht' : ω.1 = true := ht.2
  have hf' : ω.1 = false := hf.2
  simp_all

private theorem prefix_mass {p μ : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {n : ℕ} (h : Fin n → Bool) :
    (law p μ).real (atom h) = jointWeight p μ h true + jointWeight p μ h false := by
  rw [← split_value (atom h), measureReal_union (disjoint_value (atom h))
    ((measurable_atom h).inter (measurable_valueEvent false)),
    joint_mass hp0 hp1, joint_mass hp0 hp1]

private theorem posterior_cond {p μ : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {n : ℕ} (h : Fin n → Bool) :
    posterior p μ h = ((law p μ)[|atom h]).real (valueEvent true) := by
  rw [measureReal_def, cond_apply (measurable_atom h), ENNReal.toReal_mul, ENNReal.toReal_inv,
    ← measureReal_def, ← measureReal_def, prefix_mass hp0 hp1, joint_mass hp0 hp1,
    posterior, div_eq_mul_inv, mul_comm]

private theorem posterior_mem {p μ : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hμ : (μ : ℝ) < 1) {n : ℕ} (h : Fin n → Bool) :
    posterior p μ h ∈ Ioo (0 : ℝ) 1 := by
  have hx := jointWeight_pos hp0 hp1 hμ h true
  have hy := jointWeight_pos hp0 hp1 hμ h false
  have hxy := add_pos hx hy
  exact ⟨div_pos hx hxy, (div_lt_one hxy).2 (lt_add_of_pos_right _ hy)⟩

private theorem bayes_ratio {x y a b : ℝ} (hx : 0 < x) (hy : 0 < y) (ha : 0 < a)
    (hb : 0 < b) :
    x * a / (x * a + y * b) =
      (x / (x + y) * (2 * a)) / (x / (x + y) * (2 * a) + (1 - x / (x + y)) * (2 * b)) := by
  have hxy := add_pos hx hy
  have hxab := add_pos (mul_pos hx ha) (mul_pos hy hb)
  have hf : 1 - x / (x + y) = y / (x + y) := by
    field_simp
    ring
  rw [hf]
  have hh : x / (x + y) * (2 * a) + y / (x + y) * (2 * b) =
      2 * (x * a + y * b) / (x + y) := by ring
  rw [hh]
  field_simp

private theorem bayes {p μ : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hμ : (μ : ℝ) < 1) {n : ℕ} (h : Fin n → Bool) (d : Bool) :
    posterior p μ (Fin.snoc h d) =
      (posterior p μ h * (2 * likelihood μ true d)) /
        (posterior p μ h * (2 * likelihood μ true d) +
          (1 - posterior p μ h) * (2 * likelihood μ false d)) := by
  simpa only [posterior, jointWeight_snoc] using
    bayes_ratio (jointWeight_pos hp0 hp1 hμ h true) (jointWeight_pos hp0 hp1 hμ h false)
      (likelihood_pos hμ true d) (likelihood_pos hμ false d)

private theorem posterior_step_sub {p μ : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hμ : (μ : ℝ) < 1) {n : ℕ} (h : Fin n → Bool) (d : Bool) :
    let x := jointWeight p μ h true
    let y := jointWeight p μ h false
    let a := likelihood μ true d
    let b := likelihood μ false d
    posterior p μ (Fin.snoc h d) - posterior p μ h =
      x * y * (a - b) / ((x * a + y * b) * (x + y)) := by
  dsimp only
  simp only [posterior, jointWeight_snoc]
  have hx := jointWeight_pos hp0 hp1 hμ h true
  have hy := jointWeight_pos hp0 hp1 hμ h false
  have hxy := add_pos hx hy
  have hab := add_pos (mul_pos hx (likelihood_pos hμ true d))
    (mul_pos hy (likelihood_pos hμ false d))
  field_simp
  ring

private theorem quote_bracket {p μ : I} {low high : ℝ} (hV : low < high)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hμ : (μ : ℝ) < 1)
    {n : ℕ} (h : Fin n → Bool) :
    quote p μ low high h false ≤ prefixPrice p μ low high h ∧
    prefixPrice p μ low high h ≤ quote p μ low high h true ∧
    (0 < (μ : ℝ) → quote p μ low high h false < prefixPrice p μ low high h ∧
      prefixPrice p μ low high h < quote p μ low high h true) ∧
    ((μ : ℝ) = 0 → quote p μ low high h false = prefixPrice p μ low high h ∧
      prefixPrice p μ low high h = quote p μ low high h true) := by
  have hx := jointWeight_pos hp0 hp1 hμ h true
  have hy := jointWeight_pos hp0 hp1 hμ h false
  have denom (d : Bool) : 0 <
      (jointWeight p μ h true * likelihood μ true d +
        jointWeight p μ h false * likelihood μ false d) *
        (jointWeight p μ h true + jointWeight p μ h false) :=
    mul_pos (add_pos (mul_pos hx (likelihood_pos hμ true d))
      (mul_pos hy (likelihood_pos hμ false d))) (add_pos hx hy)
  have buy : likelihood μ true true - likelihood μ false true = (μ : ℝ) := by
    simp [likelihood]
    ring
  have sell : likelihood μ true false - likelihood μ false false = -(μ : ℝ) := by
    simp [likelihood]
    ring
  have step (d : Bool) :
      quote p μ low high h d - prefixPrice p μ low high h =
        (high - low) *
          (jointWeight p μ h true * jointWeight p μ h false *
            (likelihood μ true d - likelihood μ false d) /
              ((jointWeight p μ h true * likelihood μ true d +
                jointWeight p μ h false * likelihood μ false d) *
                (jointWeight p μ h true + jointWeight p μ h false))) := by
    simp only [quote, prefixPrice, add_sub_add_left_eq_sub, ← mul_sub]
    rw [posterior_step_sub hp0 hp1 hμ]
  have hdelta := sub_pos.mpr hV
  have hxy := mul_pos hx hy
  have hμ0 := μ.2.1
  refine ⟨sub_nonpos.mp ?_, sub_nonneg.mp ?_, ?_, ?_⟩
  · rw [step, sell]
    exact mul_nonpos_of_nonneg_of_nonpos hdelta.le
      (div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hxy.le (neg_nonpos.mpr hμ0)) (denom false).le)
  · rw [step, buy]
    exact mul_nonneg hdelta.le (div_nonneg (mul_nonneg hxy.le hμ0) (denom true).le)
  · intro hμ'
    refine ⟨sub_neg.mp ?_, sub_pos.mp ?_⟩
    · rw [step, sell]
      exact mul_neg_of_pos_of_neg hdelta
        (div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hxy (neg_neg_of_pos hμ')) (denom false))
    · rw [step, buy]
      exact mul_pos hdelta (div_pos (mul_pos hxy hμ') (denom true))
  · intro hμ'
    refine ⟨sub_eq_zero.mp ?_, (sub_eq_zero.mp ?_).symm⟩
    · simp [step, sell, hμ']
    · simp [step, buy, hμ']

private theorem integrable_finite_composition {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [Finite β] {ν : Measure α} [IsFiniteMeasure ν]
    {f : α → β} (hf : Measurable f) (g : β → ℝ) : Integrable (g ∘ f) ν := by
  classical
  let _ := Fintype.ofFinite β
  have hg : Measurable g := Measurable.of_discrete
  refine (integrable_const (∑ b, ‖g b‖)).mono' (hg.comp hf).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun a ↦
    Finset.single_le_sum (f := fun b ↦ ‖g b‖) (fun b _ ↦ norm_nonneg (g b)) (Finset.mem_univ (f a))

private theorem integrable_value (p μ : I) (low high : ℝ) : Integrable (value low high) (law p μ) :=
  integrable_finite_composition measurable_fst (fun b : Bool ↦ if b then high else low)

private theorem stronglyAdapted_price (p μ : I) (low high : ℝ) :
    StronglyAdapted orderFiltration (transactionPrice p μ low high) := fun n ↦
  (Measurable.of_discrete.comp (comap_measurable (history n))).stronglyMeasurable

private theorem atom_integral_value {p μ : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (low high : ℝ) {n : ℕ} (h : Fin n → Bool) :
    ∫ ω in atom h, value low high ω ∂law p μ =
      jointWeight p μ h true * high + jointWeight p μ h false * low := by
  have hA (v : Bool) : MeasurableSet (atom h ∩ valueEvent v) :=
    (measurable_atom h).inter (measurable_valueEvent v)
  have hI (v : Bool) : IntegrableOn (value low high) (atom h ∩ valueEvent v) (law p μ) :=
    (integrable_value p μ low high).integrableOn
  calc
    _ = (∫ ω in atom h ∩ valueEvent true, value low high ω ∂law p μ) +
          (∫ ω in atom h ∩ valueEvent false, value low high ω ∂law p μ) := by
      rw [← setIntegral_union (disjoint_value (atom h)) (hA false) (hI true) (hI false),
        split_value]
    _ = _ := by
      have hconst (v : Bool) : Set.EqOn (value low high)
          (fun _ ↦ if v then high else low) (atom h ∩ valueEvent v) := by
        intro ω hw
        have hv : ω.1 = v := hw.2
        simp [value, hv]
      rw [setIntegral_congr_fun (hA true) (hconst true),
        setIntegral_congr_fun (hA false) (hconst false), setIntegral_const, setIntegral_const,
        joint_mass hp0 hp1, joint_mass hp0 hp1]
      rfl

private theorem atom_integral_price {p μ : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hμ : (μ : ℝ) < 1) (low high : ℝ) {n : ℕ} (h : Fin n → Bool) :
    ∫ ω in atom h, transactionPrice p μ low high n ω ∂law p μ =
      ∫ ω in atom h, value low high ω ∂law p μ := by
  have hconst : Set.EqOn (transactionPrice p μ low high n) (fun _ ↦ prefixPrice p μ low high h)
      (atom h) := by
    intro ω hw
    have hh : history n ω = h := hw
    simp [transactionPrice, hh]
  rw [setIntegral_congr_fun (measurable_atom h) hconst, setIntegral_const, smul_eq_mul,
    prefix_mass hp0 hp1, atom_integral_value hp0 hp1, prefixPrice, posterior]
  have hsum := add_pos (jointWeight_pos hp0 hp1 hμ h true) (jointWeight_pos hp0 hp1 hμ h false)
  field_simp
  ring

private theorem price_condExp {p μ : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hμ : (μ : ℝ) < 1) (low high : ℝ) (n : ℕ) :
    transactionPrice p μ low high n =ᵐ[law p μ] (law p μ)[value low high | orderFiltration n] := by
  classical
  have hI : Integrable (transactionPrice p μ low high n) (law p μ) :=
    integrable_finite_composition (measurable_history n) (prefixPrice p μ low high)
  refine ae_eq_condExp_of_forall_setIntegral_eq (orderFiltration.le n)
    (integrable_value p μ low high) (fun _ _ _ ↦ hI.integrableOn) ?_
    ((stronglyAdapted_price p μ low high n).aestronglyMeasurable)
  intro s hs _
  obtain ⟨t, _, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  let T := t.toFinset
  have ht : history n ⁻¹' t = ⋃ h ∈ T, atom h := by
    ext ω
    simp [T, atom]
  have hd : Set.Pairwise (T : Set (Fin n → Bool)) (fun a b ↦ Disjoint (atom a) (atom b)) := by
    intro a _ b _ hab
    refine Set.disjoint_left.2 fun ω ha hb ↦ hab ?_
    exact (show history n ω = a from ha).symm.trans (show history n ω = b from hb)
  rw [ht, integral_biUnion_finset T (fun h _ ↦ measurable_atom h) hd (fun _ _ ↦ hI.integrableOn),
    integral_biUnion_finset T (fun h _ ↦ measurable_atom h) hd
      (fun _ _ ↦ (integrable_value p μ low high).integrableOn)]
  exact Finset.sum_congr rfl fun h _ ↦ atom_integral_price hp0 hp1 hμ low high h

private theorem prefixPrice_cond {p μ : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hμ : (μ : ℝ) < 1) (low high : ℝ) {n : ℕ} (h : Fin n → Bool) :
    prefixPrice p μ low high h = ∫ ω, value low high ω ∂(law p μ)[|atom h] := by
  have hsum := add_pos (jointWeight_pos hp0 hp1 hμ h true) (jointWeight_pos hp0 hp1 hμ h false)
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, ← measureReal_def,
    smul_eq_mul, prefix_mass hp0 hp1, atom_integral_value hp0 hp1, prefixPrice, posterior]
  field_simp
  ring

private theorem quote_profit {p μ : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hμ : (μ : ℝ) < 1) (low high : ℝ) {n : ℕ} (h : Fin n → Bool) (d : Bool) (q : ℝ) :
    (∫ ω, (if d then q - value low high ω else value low high ω - q)
      ∂(law p μ)[|atom (Fin.snoc h d)]) = 0 ↔ q = quote p μ low high h d := by
  let ν := (law p μ)[|atom (Fin.snoc h d)]
  have hne : law p μ (atom (Fin.snoc h d)) ≠ 0 := by
    intro hz
    have hpos := add_pos (jointWeight_pos hp0 hp1 hμ (Fin.snoc h d) true)
      (jointWeight_pos hp0 hp1 hμ (Fin.snoc h d) false)
    rw [← prefix_mass hp0 hp1, measureReal_def, hz, ENNReal.toReal_zero] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos
  have : IsProbabilityMeasure ν := cond_isProbabilityMeasure hne
  have hi : Integrable (value low high) ν :=
    integrable_finite_composition measurable_fst (fun b : Bool ↦ if b then high else low)
  have hq : quote p μ low high h d = ∫ ω, value low high ω ∂ν :=
    prefixPrice_cond hp0 hp1 hμ low high (Fin.snoc h d)
  have hone : ν.real univ = 1 := by simp [measureReal_def]
  change (∫ ω, (if d then q - value low high ω else value low high ω - q) ∂ν) = 0 ↔ _
  cases d
  · change (∫ ω, value low high ω - q ∂ν) = 0 ↔ _
    rw [integral_sub hi (integrable_const q), integral_const, hone, one_smul, ← hq,
      sub_eq_zero, eq_comm]
  · change (∫ ω, q - value low high ω ∂ν) = 0 ↔ _
    rw [integral_sub (integrable_const q) hi, integral_const, hone, one_smul, ← hq, sub_eq_zero]

private theorem atom_snoc {n : ℕ} (h : Fin n → Bool) (d : Bool) :
    atom (Fin.snoc h d) = atom h ∩ order n ⁻¹' {d} := by
  ext ω
  change history (n + 1) ω = Fin.snoc h d ↔ history n ω = h ∧ order n ω = d
  rw [history_succ]
  constructor
  · intro he
    refine ⟨funext fun i ↦ ?_, ?_⟩
    · simpa using congrFun he i.castSucc
    · simpa using congrFun he (Fin.last n)
  · rintro ⟨hh, hd⟩
    rw [hh, hd]

private theorem periodPair_law (p μ : I) (n : ℕ) :
    (law p μ).map (fun ω ↦ ω.2 n) = periodLaw μ := by
  change (law p μ).map ((fun x ↦ x n) ∘ Prod.snd) = _
  rw [← Measure.map_map (measurable_pi_apply n) measurable_snd, law, Measure.map_snd_prod,
    measure_univ, one_smul, Measure.infinitePi_map_eval]

private theorem independent_draws (p μ : I) :
    IndepFun Prod.fst Prod.snd (law p μ) ∧
      iIndepFun (fun (n : ℕ) (ω : Sample) ↦ ω.2 n) (law p μ) ∧
      (∀ n, (law p μ).map (fun ω ↦ ω.2 n) = periodLaw μ) ∧
      IndepFun Prod.fst Prod.snd (periodLaw μ) := by
  refine ⟨indepFun_prod measurable_id measurable_id, ?_, periodPair_law p μ,
    indepFun_prod measurable_id measurable_id⟩
  have hm (n : ℕ) : Measurable (fun ω : Sample ↦ ω.2 n) :=
    (measurable_pi_apply n).comp measurable_snd
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map hm]
  simp only [periodPair_law]
  change (law p μ).map Prod.snd = _
  rw [law, Measure.map_snd_prod, measure_univ, one_smul]

private theorem prefixPrice_zero (p μ : I) (low high : ℝ) (h : Fin 0 → Bool) :
    prefixPrice p μ low high h = low + (high - low) * (p : ℝ) := by
  have hsum : (p : ℝ) + (1 - (p : ℝ)) = 1 := by ring
  simp [prefixPrice, posterior, jointWeight, hsum]

/-- **Sequential Glosten–Milgrom model: quotes as conditional expectations.**
With an interior prior, values `low < high`, and an informed fraction in $[0,1)$, the value
bit is independent of the stream of mutually independent trader-type and noise-order pairs;
the bits within each pair are independent. Orders are independent given the value, with the
specified buy and sell likelihoods. Every observed prefix and both next orders have
positive mass. The posterior is interior and obeys the two Bayes updates. The bid and ask are the
unique zero-expected-profit quotes and bracket the pretrade mean, strictly with positive informed
fraction and with equality when it is zero. The transaction price selects the quote of the realized
trade, is a version of the conditional expectation on the order history, and is a martingale for
that history.

Source: L. R. Glosten and P. R. Milgrom, "Bid, ask and transaction prices in a specialist market
with heterogeneously informed traders", *Journal of Financial Economics* 14(1):71–100, 1985.
-/
public theorem sequential_quotes_and_martingale (p μ : I) (low high : ℝ)
    (hV : low < high) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hμ : (μ : ℝ) < 1) :
    (law p μ).real (valueEvent true) = p ∧
    (IndepFun Prod.fst Prod.snd (law p μ) ∧
      iIndepFun (fun (n : ℕ) (ω : Sample) ↦ ω.2 n) (law p μ) ∧
      (∀ n, (law p μ).map (fun ω ↦ ω.2 n) = periodLaw μ) ∧
      IndepFun Prod.fst Prod.snd (periodLaw μ)) ∧
    (∀ v, iIndepFun order ((law p μ)[|valueEvent v]) ∧
      ∀ n d, ((law p μ)[|valueEvent v]).real (order n ⁻¹' {d}) = likelihood μ v d) ∧
    (∀ (n : ℕ) (h : Fin n → Bool),
      let θ := posterior p μ h
      0 < (law p μ).real (atom h) ∧
      θ = ((law p μ)[|atom h]).real (valueEvent true) ∧ θ ∈ Ioo (0 : ℝ) 1 ∧
      prefixPrice p μ low high h = (∫ ω, value low high ω ∂(law p μ)[|atom h]) ∧
      posterior p μ (Fin.snoc h true) =
        θ * (1 + (μ : ℝ)) / (θ * (1 + (μ : ℝ)) + (1 - θ) * (1 - (μ : ℝ))) ∧
      posterior p μ (Fin.snoc h false) =
        θ * (1 - (μ : ℝ)) / (θ * (1 - (μ : ℝ)) + (1 - θ) * (1 + (μ : ℝ))) ∧
      (∀ d, atom (Fin.snoc h d) = atom h ∩ order n ⁻¹' {d} ∧
        0 < (law p μ).real (atom (Fin.snoc h d)) ∧
        quote p μ low high h d = (∫ ω, value low high ω ∂(law p μ)[|atom (Fin.snoc h d)]) ∧
        ∀ q : ℝ, (∫ ω, (if d then q - value low high ω else value low high ω - q)
          ∂(law p μ)[|atom (Fin.snoc h d)]) = 0 ↔ q = quote p μ low high h d) ∧
      quote p μ low high h false ≤ prefixPrice p μ low high h ∧
      prefixPrice p μ low high h ≤ quote p μ low high h true ∧
      (0 < (μ : ℝ) → quote p μ low high h false < prefixPrice p μ low high h ∧
        prefixPrice p μ low high h < quote p μ low high h true) ∧
      ((μ : ℝ) = 0 → quote p μ low high h false = prefixPrice p μ low high h ∧
        prefixPrice p μ low high h = quote p μ low high h true)) ∧
    (∀ ω, transactionPrice p μ low high 0 ω = low + (high - low) * (p : ℝ)) ∧
    (∀ n, transactionPrice p μ low high n =ᵐ[law p μ]
      (law p μ)[value low high | orderFiltration n]) ∧
    (∀ n ω, transactionPrice p μ low high (n + 1) ω =
      quote p μ low high (history n ω) (order n ω)) ∧
    Martingale (transactionPrice p μ low high) orderFiltration (law p μ) := by
  have hmass (n : ℕ) (h : Fin n → Bool) : 0 < (law p μ).real (atom h) := by
    rw [prefix_mass hp0 hp1]
    exact add_pos (jointWeight_pos hp0 hp1 hμ h true) (jointWeight_pos hp0 hp1 hμ h false)
  have hscale (v d : Bool) : 2 * likelihood μ v d =
      if v = d then 1 + (μ : ℝ) else 1 - (μ : ℝ) := by
    unfold likelihood
    split <;> ring
  refine ⟨by simpa using valueEvent_mass p μ true, independent_draws p μ,
    conditional_orders hp0 hp1, ?_, fun ω ↦ prefixPrice_zero p μ low high (history 0 ω),
    price_condExp hp0 hp1 hμ low high, ?_, ?_⟩
  · intro n h
    refine ⟨hmass n h, posterior_cond hp0 hp1 h, posterior_mem hp0 hp1 hμ h,
      prefixPrice_cond hp0 hp1 hμ low high h, ?_, ?_, ?_, quote_bracket hV hp0 hp1 hμ h⟩
    · simpa [hscale] using bayes hp0 hp1 hμ h true
    · simpa [hscale] using bayes hp0 hp1 hμ h false
    · intro d
      exact ⟨atom_snoc h d, hmass _ _, prefixPrice_cond hp0 hp1 hμ low high _,
        quote_profit hp0 hp1 hμ low high h d⟩
  · intro n ω
    simp only [transactionPrice, quote, history_succ]
  · exact (martingale_condExp (value low high) orderFiltration (law p μ)).congr
      (stronglyAdapted_price p μ low high) (fun n ↦ (price_condExp hp0 hp1 hμ low high n).symm)

end MathlibExt.Probability.Finance.GlostenMilgrom
