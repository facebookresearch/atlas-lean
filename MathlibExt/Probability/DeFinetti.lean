/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

@[expose] public section

section
open MeasureTheory Set

namespace MathlibExt.Probability.DeFinettiWanted

/-!
# Binary de Finetti representation theorem

The binary de Finetti representation of exchangeable
`ℕ → Bool` laws as mixtures of i.i.d. Bernoulli laws.
-/

/-- Cylinder set: `ω (p s) = β s` for all `s`. -/
private def dfbCyl {ι : Type*} [Fintype ι] (p : ι → ℕ) (β : ι → Bool) : Set (ℕ → Bool) :=
  {ω : ℕ → Bool | ∀ s, ω (p s) = β s}

/-- Pattern: true on left, false on right. -/
private def dfbPattern (a b : ℕ) : Fin a ⊕ Fin b → Bool :=
  Sum.elim (fun _ => true) (fun _ => false)

/-- Count of ones among first `N` coordinates, as a real. -/
private noncomputable def dfbCount (N : ℕ) (ω : ℕ → Bool) : ℝ :=
  ∑ i : Fin N, (if ω (i : ℕ) = true then (1 : ℝ) else 0)

/-- Empirical frequency, projected into `[0,1]`. -/
private noncomputable def dfbFreq (N : ℕ) (ω : ℕ → Bool) : Set.Icc (0 : ℝ) 1 :=
  Set.projIcc 0 1 (by simp) (dfbCount N ω / (N : ℝ))

/-- Moment monomial as bounded continuous function on `[0,1]`. -/
private noncomputable def dfbMoment (a b : ℕ) : C(Set.Icc (0 : ℝ) 1, ℝ) :=
  BoundedContinuousFunction.mkOfCompact
    ⟨(fun p : Set.Icc (0 : ℝ) 1 => (p.val : ℝ) ^ a * (1 - (p.val : ℝ)) ^ b),
     by fun_prop⟩

private theorem dfb_cyl_measurableSet {ι : Type*} [Fintype ι] (p : ι → ℕ) (β : ι → Bool) :
    MeasurableSet (dfbCyl p β) := by
  have : dfbCyl p β = ⋂ s, (fun ω : ℕ → Bool => ω (p s)) ⁻¹' {β s} := by
    ext ω
    simp [dfbCyl, Set.mem_iInter]
  rw [this]
  exact MeasurableSet.iInter (fun s =>
    (measurable_pi_apply (p s)) (measurableSet_singleton _))

private theorem exists_perm_finite_support_comp_eq {ι : Type*} [Finite ι]
    (f g : ι → ℕ) (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ σ : Equiv.Perm ℕ, Set.Finite {n : ℕ | σ n ≠ n} ∧ ∀ i, σ (g i) = f i := by
  classical
  have := Fintype.ofFinite ι
  set M : ℕ := Finset.univ.sup f + Finset.univ.sup g + 1 with hMdef
  have hMf : ∀ i, f i < M := fun i => by
    have h := Finset.le_sup (s := Finset.univ) (f := f) (Finset.mem_univ i)
    omega
  have hMg : ∀ i, g i < M := fun i => by
    have h := Finset.le_sup (s := Finset.univ) (f := g) (Finset.mem_univ i)
    omega
  set T : Type := {n : ℕ // n < M} with hTdef
  have hFin : Fintype T :=
    Fintype.ofEquiv (Fin M)
      { toFun := fun i => ⟨(i : ℕ), i.isLt⟩
        invFun := fun x => ⟨x.val, x.property⟩
        left_inv := fun i => by simp
        right_inv := fun x => by simp }
  have := hFin
  set f' : ι → T := fun i => ⟨f i, hMf i⟩ with hf'def
  set g' : ι → T := fun i => ⟨g i, hMg i⟩ with hg'def
  have hf'inj : Function.Injective f' := fun a b h => hf (congrArg Subtype.val h)
  have hg'inj : Function.Injective g' := fun a b h => hg (congrArg Subtype.val h)
  set e : {x : T // x ∈ Set.range g'} ≃ {x : T // x ∈ Set.range f'} :=
    (Equiv.ofInjective g' hg'inj).symm.trans (Equiv.ofInjective f' hf'inj) with hedef
  set τ : Equiv.Perm T := e.extendSubtype with hτdef
  set σ : Equiv.Perm ℕ := Equiv.Perm.ofSubtype τ with hσdef
  refine ⟨σ, ?_, ?_⟩
  · apply Set.Finite.subset (Set.finite_lt_nat M)
    intro n hn
    simp only [Set.mem_ofPred_eq] at hn ⊢
    by_contra hcon
    push Not at hcon
    exact hn (Equiv.Perm.ofSubtype_apply_of_not_mem τ (by omega : ¬ n < M))
  · intro i
    have hmem : (g i) < M := hMg i
    have h1 : σ (g i) = ((τ ⟨g i, hmem⟩ : T) : ℕ) :=
      Equiv.Perm.ofSubtype_apply_of_mem τ hmem
    rw [h1]
    have hmemT : (⟨g i, hmem⟩ : T) ∈ Set.range g' := ⟨i, rfl⟩
    have h2 : τ ⟨g i, hmem⟩ = ((e ⟨⟨g i, hmem⟩, hmemT⟩ : {x : T // x ∈ Set.range f'}) : T) :=
      Equiv.extendSubtype_apply_of_mem e _ hmemT
    rw [h2]
    have he : e ⟨⟨g i, hmem⟩, hmemT⟩ = ⟨⟨f i, hMf i⟩, ⟨i, rfl⟩⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      simp [hedef, f', g']
    rw [he]

-- N3
private theorem measure_dfb_cyl_eq_of_injective {ι : Type*} [Fintype ι]
    (μ : ProbabilityMeasure (ℕ → Bool))
    (hμ : ∀ (σ : Equiv.Perm ℕ), Set.Finite {n : ℕ | σ n ≠ n} →
      Measure.map (fun ω : ℕ → Bool => ω ∘ ⇑σ) (μ : Measure (ℕ → Bool)) =
        (μ : Measure (ℕ → Bool)))
    (f g : ι → ℕ) (β : ι → Bool)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    (μ : Measure (ℕ → Bool)) (dfbCyl f β) = (μ : Measure (ℕ → Bool)) (dfbCyl g β) := by
  classical
  obtain ⟨σ, hfin, hσ⟩ := exists_perm_finite_support_comp_eq f g hf hg
  have hmeas : Measurable (fun ω : ℕ → Bool => ω ∘ ⇑σ) :=
    Measurable.of_eval (fun i => measurable_pi_apply (σ i))
  have hpre : (fun ω : ℕ → Bool => ω ∘ ⇑σ) ⁻¹' (dfbCyl g β) = dfbCyl f β := by
    ext ω
    constructor
    · intro h s
      have hs := h s
      simp only at hs ⊢
      -- hs : (ω ∘ σ) (g s) = β s
      simp only [Function.comp_apply] at hs
      rw [← hσ s]
      exact hs
    · intro h s
      simp only [dfbCyl, Set.mem_ofPred_eq] at h ⊢
      simp only [Function.comp_apply]
      rw [hσ s]
      exact h s
  calc (μ : Measure (ℕ → Bool)) (dfbCyl f β)
      = (μ : Measure (ℕ → Bool)) ((fun ω : ℕ → Bool => ω ∘ ⇑σ) ⁻¹' (dfbCyl g β)) := by
        rw [hpre]
    _ = Measure.map (fun ω : ℕ → Bool => ω ∘ ⇑σ) (μ : Measure (ℕ → Bool)) (dfbCyl g β) := by
        rw [MeasureTheory.Measure.map_apply hmeas (dfb_cyl_measurableSet g β)]
    _ = (μ : Measure (ℕ → Bool)) (dfbCyl g β) := by
        rw [hμ σ hfin]

private theorem dfb_count_pow_mul_eq_sum (N a b : ℕ) (ω : ℕ → Bool) :
    (∑ i : Fin N, (if ω (i : ℕ) = true then (1 : ℝ) else 0)) ^ a *
    (∑ i : Fin N, (1 - (if ω (i : ℕ) = true then (1 : ℝ) else 0))) ^ b =
    ∑ p : (Fin a ⊕ Fin b → Fin N),
      (if ∀ s, ω ((p s : Fin N) : ℕ) = dfbPattern a b s then (1 : ℝ) else 0) := by
  classical
  have hL : ∀ a' : Fin a,
      (∑ j : Fin N, (if ω ((j : Fin N) : ℕ) = dfbPattern a b (Sum.inl a')
        then (1 : ℝ) else 0)) =
      (∑ i : Fin N, (if ω ((i : Fin N) : ℕ) = true then (1 : ℝ) else 0)) :=
    fun a' => rfl
  have hR : ∀ b' : Fin b,
      (∑ j : Fin N, (if ω ((j : Fin N) : ℕ) = dfbPattern a b (Sum.inr b')
        then (1 : ℝ) else 0)) =
      (∑ i : Fin N, (1 - (if ω ((i : Fin N) : ℕ) = true then (1 : ℝ) else 0))) := by
    intro b'
    apply Finset.sum_congr rfl
    intro j _
    have hpat : dfbPattern a b (Sum.inr b') = false := rfl
    rw [hpat]
    cases ω ((j : Fin N) : ℕ) <;> simp
  have hterm : ∀ p : (Fin a ⊕ Fin b → Fin N),
      (if ∀ s, ω ((p s : Fin N) : ℕ) = dfbPattern a b s then (1 : ℝ) else 0) =
      ∏ s : Fin a ⊕ Fin b,
        (if ω ((p s : Fin N) : ℕ) = dfbPattern a b s then (1 : ℝ) else 0) := by
    intro p
    have hpb := Finset.prod_boole (M₀ := ℝ)
      (s := (Finset.univ : Finset (Fin a ⊕ Fin b)))
      (p := fun s : Fin a ⊕ Fin b => ω ((p s : Fin N) : ℕ) = dfbPattern a b s)
    simpa using hpb.symm
  have hRHS : (∑ p : (Fin a ⊕ Fin b → Fin N),
        (if ∀ s, ω ((p s : Fin N) : ℕ) = dfbPattern a b s then (1 : ℝ) else 0)) =
      ∏ s : Fin a ⊕ Fin b, ∑ j : Fin N,
        (if ω ((j : Fin N) : ℕ) = dfbPattern a b s then (1 : ℝ) else 0) := by
    calc (∑ p : (Fin a ⊕ Fin b → Fin N),
            (if ∀ s, ω ((p s : Fin N) : ℕ) = dfbPattern a b s then (1 : ℝ) else 0))
        = (∑ p : (Fin a ⊕ Fin b → Fin N), ∏ s : Fin a ⊕ Fin b,
            (if ω ((p s : Fin N) : ℕ) = dfbPattern a b s then (1 : ℝ) else 0)) :=
          Finset.sum_congr rfl (fun p _ => hterm p)
      _ = ∏ s : Fin a ⊕ Fin b, ∑ j : Fin N,
            (if ω ((j : Fin N) : ℕ) = dfbPattern a b s then (1 : ℝ) else 0) :=
          (Fintype.prod_sum
            (fun s : Fin a ⊕ Fin b => fun j : Fin N =>
              (if ω ((j : Fin N) : ℕ) = dfbPattern a b s then (1 : ℝ) else 0))).symm
  rw [hRHS, Fintype.prod_sum_type]
  have hPL : (∏ a' : Fin a, ∑ j : Fin N,
      (if ω ((j : Fin N) : ℕ) = dfbPattern a b (Sum.inl a') then (1 : ℝ) else 0)) =
      (∑ i : Fin N, (if ω ((i : Fin N) : ℕ) = true then (1 : ℝ) else 0)) ^ a := by
    rw [Finset.prod_congr rfl (fun a' _ => hL a')]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hPR : (∏ b' : Fin b, ∑ j : Fin N,
      (if ω ((j : Fin N) : ℕ) = dfbPattern a b (Sum.inr b') then (1 : ℝ) else 0)) =
      (∑ i : Fin N, (1 - (if ω ((i : Fin N) : ℕ) = true then (1 : ℝ) else 0))) ^ b := by
    rw [Finset.prod_congr rfl (fun b' _ => hR b')]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hPL, hPR]

-- N5
private theorem abs_sum_sub_pow_mul_le_of_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (t : (ι → Fin N) → ℝ) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (ht0 : ∀ p, 0 ≤ t p) (ht1 : ∀ p, t p ≤ 1)
    (htinj : ∀ p, Function.Injective p → t p = c) :
    |∑ p : (ι → Fin N), t p - (N : ℝ) ^ Fintype.card ι * c| ≤
      (N : ℝ) ^ Fintype.card ι - (Nat.descFactorial N (Fintype.card ι) : ℝ) := by
  classical
  set k : ℕ := Fintype.card ι with hkdef
  set D : ℕ := Nat.descFactorial N k with hDdef
  -- counts
  have hcard_total : Fintype.card (ι → Fin N) = N ^ k := by
    rw [Fintype.card_fun, Fintype.card_fin]
  have hcard_inj : (Finset.univ.filter (fun p : ι → Fin N => Function.Injective p)).card = D := by
    have h1 : Fintype.card {p : ι → Fin N // Function.Injective p} =
        (Finset.univ.filter (fun p : ι → Fin N => Function.Injective p)).card := by
      rw [Fintype.card_subtype, ← Set.toFinset_ofPred, Set.toFinset_card]
    rw [← h1]
    have h2 := Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding ι (Fin N))
    rw [Fintype.card_embedding_eq, Fintype.card_fin] at h2
    -- h2 : card {f // Injective f} = descFactorial N k; need k = card ι
    simp only [hDdef, hkdef] at h2 ⊢
    exact h2
  have hcard_compl : (Finset.univ.filter (fun p : ι → Fin N => ¬ Function.Injective p)).card
      = N ^ k - D := by
    have hfc := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (ι → Fin N)))
      (fun p => Function.Injective p)
    rw [hcard_inj] at hfc
    have htot : (Finset.univ : Finset (ι → Fin N)).card = N ^ k := by
      rw [Finset.card_univ, hcard_total]
    omega
  -- split the sum
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (ι → Fin N))
    (fun p => Function.Injective p) (fun p => t p)
  set R : ℝ := ∑ p ∈ Finset.univ.filter (fun p : ι → Fin N => ¬ Function.Injective p), t p with
      hRdef
  have hR0 : 0 ≤ R := Finset.sum_nonneg (fun p _ => ht0 p)
  have hRle : R ≤ ((N ^ k - D : ℕ) : ℝ) := by
    calc R ≤ (Finset.univ.filter (fun p : ι → Fin N => ¬ Function.Injective p)).card • (1 : ℝ) :=
          Finset.sum_le_card_nsmul _ _ _ (fun p _ => ht1 p)
      _ = ((N ^ k - D : ℕ) : ℝ) := by rw [hcard_compl, nsmul_eq_mul, mul_one]
  have hInj : ∑ p ∈ Finset.univ.filter (fun p : ι → Fin N => Function.Injective p), t p
      = (D : ℝ) * c := by
    have : ∑ p ∈ Finset.univ.filter (fun p : ι → Fin N => Function.Injective p), t p
        = ∑ p ∈ Finset.univ.filter (fun p : ι → Fin N => Function.Injective p), c :=
      Finset.sum_congr rfl (fun p hp => htinj p (Finset.mem_filter.mp hp).2)
    rw [this, Finset.sum_const, hcard_inj, nsmul_eq_mul]
  have hDle : D ≤ N ^ k := Nat.descFactorial_le_pow N k
  have hcast : ((N ^ k - D : ℕ) : ℝ) = (N : ℝ) ^ k - (D : ℝ) := by
    rw [Nat.cast_sub hDle, Nat.cast_pow]
  -- reassemble
  have hsum : ∑ p : (ι → Fin N), t p = (D : ℝ) * c + R := by
    have h1 : ∑ p : (ι → Fin N), t p = ∑ p ∈ Finset.univ, t p := by simp
    rw [h1, ← hsplit, hInj]
  rw [hcast] at hRle
  rw [hsum]
  -- goal: |(D:ℝ) * c + R - (N:ℝ)^k * c| ≤ (N:ℝ)^k - D
  have hMk0 : (0 : ℝ) ≤ (N : ℝ) ^ k - (D : ℝ) := by
    have : (D : ℝ) ≤ (N : ℝ) ^ k := by
      rw [← Nat.cast_pow]
      exact Nat.cast_le.mpr hDle
    linarith
  have hMc : (0 : ℝ) ≤ ((N : ℝ) ^ k - (D : ℝ)) * c ∧ ((N : ℝ) ^ k - (D : ℝ)) * c ≤ (N : ℝ) ^ k -
      (D : ℝ) := by
    constructor
    · exact mul_nonneg hMk0 hc0
    · have := mul_le_mul_of_nonneg_left hc1 hMk0
      simpa using this
  rw [abs_le]
  constructor <;> nlinarith [hR0, hRle, hMc.1, hMc.2, hc0, hc1, hMk0]

-- N6
private theorem tendsto_descFactorial_div_pow (k : ℕ) :
    Filter.Tendsto (fun N : ℕ => (Nat.descFactorial N k : ℝ) / (N : ℝ) ^ k)
      Filter.atTop (nhds 1) := by
  have hne : ∀ᶠ N : ℕ in Filter.atTop, ((N : ℝ) ^ k) ≠ 0 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact pow_ne_zero k (by exact_mod_cast ne_of_gt hN)
  exact (Asymptotics.isEquivalent_iff_tendsto_one hne).mp (isEquivalent_descFactorial k)

-- N7
private theorem integral_dfb_count_moment (μ : ProbabilityMeasure (ℕ → Bool)) (a b N : ℕ) :
    MeasureTheory.integral (μ : Measure (ℕ → Bool))
      (fun ω => dfbCount N ω ^ a * ((N : ℝ) - dfbCount N ω) ^ b) =
    ∑ p : (Fin a ⊕ Fin b → Fin N),
      (μ : Measure (ℕ → Bool)).real
        (dfbCyl (fun s => ((p s : Fin N) : ℕ)) (dfbPattern a b)) := by
  classical
  have hsub : ∀ ω : ℕ → Bool, (N : ℝ) - dfbCount N ω =
      ∑ i : Fin N, (1 - (if ω ((i : Fin N) : ℕ) = true then (1 : ℝ) else 0)) := by
    intro ω
    simp only [dfbCount]
    rw [Finset.sum_sub_distrib]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpoint : ∀ ω : ℕ → Bool, dfbCount N ω ^ a * ((N : ℝ) - dfbCount N ω) ^ b =
      ∑ p : (Fin a ⊕ Fin b → Fin N),
        (if ∀ s, ω ((p s : Fin N) : ℕ) = dfbPattern a b s then (1 : ℝ) else 0) := by
    intro ω
    rw [hsub ω]
    simp only [dfbCount]
    exact dfb_count_pow_mul_eq_sum N a b ω
  have hind : ∀ (p : Fin a ⊕ Fin b → Fin N) (ω : ℕ → Bool),
      (if ∀ s, ω ((p s : Fin N) : ℕ) = dfbPattern a b s then (1 : ℝ) else 0) =
      Set.indicator (dfbCyl (fun s => ((p s : Fin N) : ℕ)) (dfbPattern a b)) 1 ω := by
    intro p ω
    by_cases h : ω ∈ dfbCyl (fun s => ((p s : Fin N) : ℕ)) (dfbPattern a b)
    · have h' : (∀ s, ω ((p s : Fin N) : ℕ) = dfbPattern a b s) := h
      rw [Set.indicator_of_mem h, ite_eq_left h']
      rfl
    · have h' : ¬ (∀ s, ω ((p s : Fin N) : ℕ) = dfbPattern a b s) := h
      rw [Set.indicator_of_notMem h, ite_eq_right h']
  have hfun : (fun ω : ℕ → Bool => dfbCount N ω ^ a * ((N : ℝ) - dfbCount N ω) ^ b) =
      (fun ω => ∑ p : (Fin a ⊕ Fin b → Fin N),
        Set.indicator (dfbCyl (fun s => ((p s : Fin N) : ℕ)) (dfbPattern a b)) 1 ω) := by
    funext ω
    rw [hpoint ω]
    exact Finset.sum_congr rfl (fun p _ => hind p ω)
  rw [hfun]
  rw [MeasureTheory.integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro p _
    exact MeasureTheory.integral_indicator_one (dfb_cyl_measurableSet _ _)
  · intro p _
    exact (MeasureTheory.integrable_const 1).indicator (dfb_cyl_measurableSet _ _)

-- N9a
private theorem measurable_dfb_count (N : ℕ) : Measurable (dfbCount N) := by
  unfold dfbCount
  apply Finset.measurable_sum
  intro i _
  have h1 : Measurable (fun b : Bool => if b = true then (1 : ℝ) else 0) :=
    Measurable.of_discrete
  have h2 : Measurable (fun ω : ℕ → Bool => ω ((i : Fin N) : ℕ)) :=
    measurable_pi_apply _
  have heq : (fun a : ℕ → Bool => if a ((i : Fin N) : ℕ) = true then (1 : ℝ) else 0) =
      ((fun b : Bool => if b = true then (1 : ℝ) else 0) ∘
        (fun ω : ℕ → Bool => ω ((i : Fin N) : ℕ))) := rfl
  rw [heq]
  exact h1.comp h2

-- N9b
private theorem dfb_count_div_mem_Icc (N : ℕ) (ω : ℕ → Bool) :
    dfbCount N ω / (N : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  have h0 : 0 ≤ dfbCount N ω := by
    simp only [dfbCount]
    apply Finset.sum_nonneg
    intro i _
    split_ifs with h
    · exact zero_le_one
    · exact le_refl 0
  have hterm : ∀ i : Fin N,
      (if ω ((i : Fin N) : ℕ) = true then (1 : ℝ) else 0) ≤ 1 := by
    intro i
    split_ifs with h
    · exact le_refl 1
    · exact zero_le_one
  have hle : dfbCount N ω ≤ (N : ℝ) := by
    simp only [dfbCount]
    calc (∑ i : Fin N, (if ω ((i : Fin N) : ℕ) = true then (1 : ℝ) else 0))
        ≤ (Finset.univ.card) • (1 : ℝ) :=
          Finset.sum_le_card_nsmul _ _ _ (fun i _ => hterm i)
      _ = (N : ℝ) := by
          rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rcases eq_or_ne N 0 with rfl | hN
  · have hz : dfbCount 0 ω = 0 := by simp [dfbCount]
    rw [hz]
    simp [Set.mem_Icc]
  · rw [Set.mem_Icc]
    constructor
    · exact div_nonneg h0 (Nat.cast_nonneg N)
    · exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hN)).mpr hle

-- N10
private theorem integral_map_dfb_freq (μ : ProbabilityMeasure (ℕ → Bool)) (a b N : ℕ) :
    MeasureTheory.integral
      (MeasureTheory.ProbabilityMeasure.map μ (dfbFreq N) : ProbabilityMeasure (Set.Icc (0 : ℝ) 1))
      (fun p => dfbMoment a b p) =
    MeasureTheory.integral (μ : Measure (ℕ → Bool))
      (fun ω => (dfbCount N ω / (N : ℝ)) ^ a * (1 - dfbCount N ω / (N : ℝ)) ^ b) := by
  have hmeas : Measurable (dfbFreq N) := by
    have hdiv : Measurable (fun ω : ℕ → Bool => dfbCount N ω / (N : ℝ)) :=
      (measurable_dfb_count N).div_const _
    have hcont : Continuous (Set.projIcc (0 : ℝ) 1 (by norm_num : (0 : ℝ) ≤ 1)) :=
      continuous_projIcc
    have hcomp := hcont.measurable.comp hdiv
    have heq : (fun ω : ℕ → Bool => dfbFreq N ω) =
        ((Set.projIcc (0 : ℝ) 1 (by norm_num : (0 : ℝ) ≤ 1)) ∘
          (fun ω : ℕ → Bool => dfbCount N ω / (N : ℝ))) := rfl
    change Measurable (fun ω : ℕ → Bool => dfbFreq N ω)
    rw [heq]
    exact hcomp
  have hfae : MeasureTheory.AEStronglyMeasurable (fun p : Set.Icc (0 : ℝ) 1 => dfbMoment a b p)
      (MeasureTheory.Measure.map (dfbFreq N) (μ : Measure (ℕ → Bool))) :=
    (dfbMoment a b).continuous.aestronglyMeasurable
  calc MeasureTheory.integral
        (MeasureTheory.ProbabilityMeasure.map μ (dfbFreq N) : ProbabilityMeasure
            (Set.Icc (0 : ℝ) 1))
        (fun p => dfbMoment a b p)
      = MeasureTheory.integral
          (MeasureTheory.Measure.map (dfbFreq N) (μ : Measure (ℕ → Bool)))
          (fun p => dfbMoment a b p) := by
        rw [MeasureTheory.ProbabilityMeasure.toMeasure_map]
    _ = MeasureTheory.integral (μ : Measure (ℕ → Bool))
          (fun ω => dfbMoment a b (dfbFreq N ω)) :=
        MeasureTheory.integral_map hmeas.aemeasurable hfae
    _ = MeasureTheory.integral (μ : Measure (ℕ → Bool))
          (fun ω => (dfbCount N ω / (N : ℝ)) ^ a * (1 - dfbCount N ω / (N : ℝ)) ^ b) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with ω
        have hmem := dfb_count_div_mem_Icc N ω
        have hfreq : (dfbFreq N ω).val = dfbCount N ω / (N : ℝ) := by
          have h := Set.projIcc_of_mem (show (0 : ℝ) ≤ 1 by norm_num) hmem
          have h2 : dfbFreq N ω = ⟨dfbCount N ω / (N : ℝ), hmem⟩ := h
          rw [h2]
        simp only [dfbMoment, BoundedContinuousFunction.mkOfCompact_apply,
          ContinuousMap.coe_mk]
        rw [hfreq]

-- N11
private theorem exists_eq_of_tendsto_comp_of_compactSpace {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (u : ℕ → X) :
    ∃ x : X, ∀ (Φ : C(X, ℝ)) (L : ℝ),
      Filter.Tendsto (fun N => Φ (u N)) Filter.atTop (nhds L) → Φ x = L := by
  obtain ⟨x, hx⟩ := exists_clusterPt_of_compactSpace (Filter.map u Filter.atTop)
  refine ⟨x, fun Φ L hlim => ?_⟩
  have hmc : MapClusterPt (Φ x) Filter.atTop (fun N => Φ (u N)) :=
    MapClusterPt.continuousAt_comp Φ.continuous.continuousAt hx
  have hle : Filter.map (fun N => Φ (u N)) Filter.atTop ≤ nhds L := hlim
  have hcl : ClusterPt (Φ x) (nhds L) :=
    ClusterPt.mono hmc hle
  by_contra hne
  have hdis : Disjoint (nhds (Φ x)) (nhds L) := disjoint_nhds_nhds.mpr hne
  exact (clusterPt_iff_not_disjoint.mp hcl) hdis

private noncomputable def dfbQ (A B : Finset ℕ) : Fin A.card ⊕ Fin B.card → ℕ :=
  Sum.elim ⇑(Finset.orderEmbOfFin A rfl) ⇑(Finset.orderEmbOfFin B rfl)

-- N12a
private theorem dfbQ_injective (A B : Finset ℕ) (hAB : Disjoint A B) :
    Function.Injective (dfbQ A B) := by
  unfold dfbQ
  apply Function.Injective.sumElim
  · exact (Finset.orderEmbOfFin A rfl).injective
  · exact (Finset.orderEmbOfFin B rfl).injective
  · intro a b hab
    have haA : (Finset.orderEmbOfFin A rfl) a ∈ A :=
      Finset.orderEmbOfFin_mem A rfl a
    have hbB : (Finset.orderEmbOfFin B rfl) b ∈ B :=
      Finset.orderEmbOfFin_mem B rfl b
    rw [hab] at haA
    exact (Finset.disjoint_left.mp hAB haA) hbB

-- N12b
private theorem dfb_wanted_cyl_eq (A B : Finset ℕ) (_hAB : Disjoint A B) :
    {ω : ℕ → Bool | (∀ i ∈ A, ω i = true) ∧ (∀ i ∈ B, ω i = false)} =
    dfbCyl (dfbQ A B) (dfbPattern A.card B.card) := by
  ext ω
  constructor
  · intro h
    obtain ⟨hA, hB⟩ := h
    intro s
    cases s with
    | inl a =>
      exact hA _ (Finset.orderEmbOfFin_mem A rfl a)
    | inr b =>
      exact hB _ (Finset.orderEmbOfFin_mem B rfl b)
  · intro h
    constructor
    · intro i hi
      have hmem : i ∈ (↑A : Set ℕ) := Finset.mem_coe.mpr hi
      rw [← Finset.range_orderEmbOfFin A rfl] at hmem
      obtain ⟨j, hj⟩ := hmem
      have hs := h (Sum.inl j)
      rw [← hj]
      exact hs
    · intro i hi
      have hmem : i ∈ (↑B : Set ℕ) := Finset.mem_coe.mpr hi
      rw [← Finset.range_orderEmbOfFin B rfl] at hmem
      obtain ⟨j, hj⟩ := hmem
      have hs := h (Sum.inr j)
      rw [← hj]
      exact hs

-- N8
private theorem tendsto_integral_dfb_freq_moment
    (μ : ProbabilityMeasure (ℕ → Bool))
    (hμ : ∀ (σ : Equiv.Perm ℕ), Set.Finite {n : ℕ | σ n ≠ n} →
      Measure.map (fun ω : ℕ → Bool => ω ∘ ⇑σ) (μ : Measure (ℕ → Bool)) =
        (μ : Measure (ℕ → Bool)))
    (a b : ℕ) (q : Fin a ⊕ Fin b → ℕ) (hq : Function.Injective q) :
    Filter.Tendsto
      (fun N : ℕ => MeasureTheory.integral (μ : Measure (ℕ → Bool))
        (fun ω => (dfbCount N ω / (N : ℝ)) ^ a * (1 - dfbCount N ω / (N : ℝ)) ^ b))
      Filter.atTop
      (nhds ((μ : Measure (ℕ → Bool)).real (dfbCyl q (dfbPattern a b)))) := by
  classical
  have hcard : Fintype.card (Fin a ⊕ Fin b) = a + b := by simp [Fintype.card_sum]
  have hc0 : 0 ≤ (μ : Measure (ℕ → Bool)).real (dfbCyl q (dfbPattern a b)) :=
    MeasureTheory.measureReal_nonneg
  have hc1 : (μ : Measure (ℕ → Bool)).real (dfbCyl q (dfbPattern a b)) ≤ 1 :=
    MeasureTheory.measureReal_le_one
  have hpoint : ∀ N : ℕ, 1 ≤ N → ∀ ω : ℕ → Bool,
      (dfbCount N ω / (N : ℝ)) ^ a * (1 - dfbCount N ω / (N : ℝ)) ^ b =
      (dfbCount N ω ^ a * ((N : ℝ) - dfbCount N ω) ^ b) / (N : ℝ) ^ (a + b) := by
    intro N hN ω
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
    rw [one_sub_div hNr, div_pow, div_pow, div_mul_div_comm, ← pow_add]
  have hM : ∀ N : ℕ, 1 ≤ N →
      MeasureTheory.integral (μ : Measure (ℕ → Bool))
        (fun ω => (dfbCount N ω / (N : ℝ)) ^ a * (1 - dfbCount N ω / (N : ℝ)) ^ b) =
      (∑ p : (Fin a ⊕ Fin b → Fin N),
        (μ : Measure (ℕ → Bool)).real
          (dfbCyl (fun s => ((p s : Fin N) : ℕ)) (dfbPattern a b))) / (N : ℝ) ^ (a + b) := by
    intro N hN
    have hfun : (fun ω : ℕ → Bool => (dfbCount N ω / (N : ℝ)) ^ a *
        (1 - dfbCount N ω / (N : ℝ)) ^ b) =
        (fun ω => (dfbCount N ω ^ a * ((N : ℝ) - dfbCount N ω) ^ b) / (N : ℝ) ^ (a + b)) :=
      funext (fun ω => hpoint N hN ω)
    rw [hfun, MeasureTheory.integral_div, integral_dfb_count_moment]
  have hN5 : ∀ N : ℕ,
      |(∑ p : (Fin a ⊕ Fin b → Fin N),
        (μ : Measure (ℕ → Bool)).real
          (dfbCyl (fun s => ((p s : Fin N) : ℕ)) (dfbPattern a b))) -
        (N : ℝ) ^ (a + b) *
          (μ : Measure (ℕ → Bool)).real (dfbCyl q (dfbPattern a b))| ≤
        (N : ℝ) ^ (a + b) - ((Nat.descFactorial N (a + b) : ℕ) : ℝ) := by
    intro N
    have htinj : ∀ p : (Fin a ⊕ Fin b → Fin N), Function.Injective p →
        (μ : Measure (ℕ → Bool)).real
          (dfbCyl (fun s => ((p s : Fin N) : ℕ)) (dfbPattern a b)) =
        (μ : Measure (ℕ → Bool)).real (dfbCyl q (dfbPattern a b)) := by
      intro p hp
      have hinj : Function.Injective (fun s => ((p s : Fin N) : ℕ)) :=
        Fin.val_injective.comp hp
      have hN3 := measure_dfb_cyl_eq_of_injective μ hμ
        (fun s => ((p s : Fin N) : ℕ)) q (dfbPattern a b) hinj hq
      rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def]
      exact congrArg ENNReal.toReal hN3
    have h := abs_sum_sub_pow_mul_le_of_injective N
      (fun p : (Fin a ⊕ Fin b → Fin N) =>
        (μ : Measure (ℕ → Bool)).real
          (dfbCyl (fun s => ((p s : Fin N) : ℕ)) (dfbPattern a b)))
      ((μ : Measure (ℕ → Bool)).real (dfbCyl q (dfbPattern a b)))
      hc0 hc1
      (fun p => MeasureTheory.measureReal_nonneg)
      (fun p => MeasureTheory.measureReal_le_one)
      htinj
    rwa [hcard] at h
  have alg : ∀ (T Y D cc : ℝ), 0 < Y → |T - Y * cc| ≤ Y - D →
      |T / Y - cc| ≤ 1 - D / Y := by
    intro T Y D cc hY hle
    have hYne : Y ≠ 0 := ne_of_gt hY
    have hrew : T / Y - cc = (T - Y * cc) / Y := by
      field_simp
    rw [hrew, abs_div, abs_of_pos hY, div_le_iff₀ hY]
    have hDeq : (1 - D / Y) * Y = Y - D := by
      field_simp
    rw [hDeq]
    exact hle
  have hbound : ∀ N : ℕ, 1 ≤ N →
      |MeasureTheory.integral (μ : Measure (ℕ → Bool))
        (fun ω => (dfbCount N ω / (N : ℝ)) ^ a * (1 - dfbCount N ω / (N : ℝ)) ^ b) -
        (μ : Measure (ℕ → Bool)).real (dfbCyl q (dfbPattern a b))| ≤
        1 - ((Nat.descFactorial N (a + b) : ℕ) : ℝ) / (N : ℝ) ^ (a + b) := by
    intro N hN
    have hNr : (0 : ℝ) < (N : ℝ) ^ (a + b) := by
      have h1 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      exact pow_pos h1 _
    rw [hM N hN]
    exact alg _ _ _ _ hNr (hN5 N)
  have hg : Filter.Tendsto
      (fun N : ℕ => 1 - ((Nat.descFactorial N (a + b) : ℕ) : ℝ) / (N : ℝ) ^ (a + b))
      Filter.atTop (nhds 0) := by
    have h1 := tendsto_descFactorial_div_pow (a + b)
    have h2 := Filter.Tendsto.const_sub (1 : ℝ) h1
    simpa using h2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards with N
    exact norm_nonneg _
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    rw [Real.norm_eq_abs]
    exact hbound N hN

-- N13: the Wanted statement, verbatim
/--
**De Finetti's theorem for binary sequences.** Let $\mu$ be a probability measure on the space
$\{0, 1\}^{\mathbb{N}}$ of binary sequences $\omega = (\omega_i)_{i \in \mathbb{N}}$, with $0$ and
$1$ standing for false and true. Suppose $\mu$ is exchangeable: for every permutation $\pi$ of
$\mathbb{N}$ that moves only finitely many points, the image of $\mu$ under the map
$\omega \mapsto \omega \circ \pi$ is $\mu$. Then there is a probability measure $\nu$ on $[0, 1]$
such that for all disjoint finite sets $A, B \subseteq \mathbb{N}$,
$$\mu\{\omega : \omega_i = 1 \text{ for all } i \in A \text{ and } \omega_i = 0 \text{ for all }
i \in B\} = \int_{[0, 1]} p^{|A|} (1 - p)^{|B|} \, d\nu(p).$$

Proves `Wanted` entry `deFinetti_binary`.

Source: B. de Finetti, Funzione caratteristica di un fenomeno aleatorio, Atti Accad.
Naz. Lincei 4 (1931) and La prévision: ses lois logiques (1937); textbook in Kallenberg,
Probabilistic Symmetries and Invariance Principles; also Durrett, Probability Theory and Examples
-/
theorem deFinetti_binary
    (μ : ProbabilityMeasure (ℕ → Bool))
    (hμ : ∀ (σ : Equiv.Perm ℕ), Set.Finite {n : ℕ | σ n ≠ n} →
      Measure.map (fun ω : ℕ → Bool => ω ∘ ⇑σ) (μ : Measure (ℕ → Bool)) =
        (μ : Measure (ℕ → Bool))) :
    ∃ (ν : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)),
      ∀ (A B : Finset ℕ), Disjoint A B →
        (μ : Measure (ℕ → Bool))
          {ω : ℕ → Bool | (∀ i ∈ A, ω i = true) ∧ (∀ i ∈ B, ω i = false)} =
          ENNReal.ofReal
            (MeasureTheory.integral (ν : Measure (Set.Icc (0 : ℝ) 1))
              (fun p : Set.Icc (0 : ℝ) 1 =>
                (p.val : ℝ) ^ A.card * (1 - (p.val : ℝ)) ^ B.card)) := by
  obtain ⟨ν, hν⟩ := exists_eq_of_tendsto_comp_of_compactSpace
    (fun N : ℕ => MeasureTheory.ProbabilityMeasure.map μ (dfbFreq N))
  refine ⟨ν, fun A B hAB => ?_⟩
  have hqinj : Function.Injective (dfbQ A B) := dfbQ_injective A B hAB
  have hset := dfb_wanted_cyl_eq A B hAB
  have hΦcont : Continuous (fun ν' : ProbabilityMeasure (Set.Icc (0 : ℝ) 1) =>
      MeasureTheory.integral (ν' : Measure (Set.Icc (0 : ℝ) 1))
        (fun p : Set.Icc (0 : ℝ) 1 => dfbMoment A.card B.card p)) :=
    MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction _
  have hlim : Filter.Tendsto
      (fun N : ℕ => MeasureTheory.integral
        ((MeasureTheory.ProbabilityMeasure.map μ (dfbFreq N) :
          ProbabilityMeasure (Set.Icc (0 : ℝ) 1)) : Measure (Set.Icc (0 : ℝ) 1))
        (fun p : Set.Icc (0 : ℝ) 1 => dfbMoment A.card B.card p))
      Filter.atTop
      (nhds ((μ : Measure (ℕ → Bool)).real
        (dfbCyl (dfbQ A B) (dfbPattern A.card B.card)))) := by
    have h8 := tendsto_integral_dfb_freq_moment μ hμ A.card B.card (dfbQ A B) hqinj
    refine Filter.Tendsto.congr (fun N => ?_) h8
    exact (integral_map_dfb_freq μ A.card B.card N).symm
  have hval : MeasureTheory.integral (ν : Measure (Set.Icc (0 : ℝ) 1))
      (fun p : Set.Icc (0 : ℝ) 1 => dfbMoment A.card B.card p) =
      (μ : Measure (ℕ → Bool)).real
        (dfbCyl (dfbQ A B) (dfbPattern A.card B.card)) :=
    hν ⟨_, hΦcont⟩ _ hlim
  have hval2 : MeasureTheory.integral (ν : Measure (Set.Icc (0 : ℝ) 1))
      (fun p : Set.Icc (0 : ℝ) 1 =>
        (p.val : ℝ) ^ A.card * (1 - (p.val : ℝ)) ^ B.card) =
      (μ : Measure (ℕ → Bool)).real
        (dfbCyl (dfbQ A B) (dfbPattern A.card B.card)) := by
    have hfun : (fun p : Set.Icc (0 : ℝ) 1 => dfbMoment A.card B.card p) =
        (fun p : Set.Icc (0 : ℝ) 1 =>
          (p.val : ℝ) ^ A.card * (1 - (p.val : ℝ)) ^ B.card) := by
      funext p
      simp only [dfbMoment, BoundedContinuousFunction.mkOfCompact_apply,
        ContinuousMap.coe_mk]
    rwa [hfun] at hval
  rw [hset, hval2, MeasureTheory.measureReal_def,
    ENNReal.ofReal_toReal (MeasureTheory.measure_ne_top _ _)]

end MathlibExt.Probability.DeFinettiWanted
end
