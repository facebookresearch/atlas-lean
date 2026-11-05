/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Computability.RE
public import Mathlib.NumberTheory.Dioph
import Mathlib.Computability.Primrec.Basic
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Logic.Godel.GodelBetaFunction
import Mathlib.Tactic

open scoped Dioph Vector3 Nat Function

namespace MathlibExt.NumberTheory.DPRMWanted

/-- Natural-number polynomial expressions in variables `γ`. -/
private inductive dpNatPoly {γ : Type} : ((γ → ℕ) → ℕ) → Prop
  | var (i : γ) : dpNatPoly (fun v => v i)
  | const (n : ℕ) : dpNatPoly (fun _ => n)
  | add {F₁ F₂ : (γ → ℕ) → ℕ} :
      dpNatPoly F₁ → dpNatPoly F₂ → dpNatPoly (fun v => F₁ v + F₂ v)
  | mul {F₁ F₂ : (γ → ℕ) → ℕ} :
      dpNatPoly F₁ → dpNatPoly F₂ → dpNatPoly (fun v => F₁ v * F₂ v)

private theorem dpNatPoly_mono {γ : Type} {F : (γ → ℕ) → ℕ}
    (hF : dpNatPoly F) : ∀ {v w : γ → ℕ}, (∀ i, v i ≤ w i) → F v ≤ F w := by
  induction hF with
  | var i => intro v w hle; exact hle i
  | const n => intro v w hle; exact le_rfl
  | add _ _ ih1 ih2 => intro v w hle; exact Nat.add_le_add (ih1 hle) (ih2 hle)
  | mul _ _ ih1 ih2 => intro v w hle; exact Nat.mul_le_mul (ih1 hle) (ih2 hle)

private theorem dpNatPoly_diophFn {γ : Type} {F : (γ → ℕ) → ℕ}
    (hF : dpNatPoly F) : Dioph.DiophFn F := by
  induction hF with
  | var i => exact Dioph.proj_dioph i
  | const n => exact Dioph.const_dioph n
  | add _ _ ih1 ih2 => exact Dioph.add_dioph ih1 ih2
  | mul _ _ ih1 ih2 => exact Dioph.mul_dioph ih1 ih2

private theorem dpNatPoly_primrec {γ σ : Type} [Primcodable σ]
    {r : γ → σ → ℕ} (hr : ∀ i, Primrec (r i))
    {F : (γ → ℕ) → ℕ} (hF : dpNatPoly F) :
    Primrec (fun s => F (fun i => r i s)) := by
  induction hF with
  | var i => exact hr i
  | const n => exact Primrec.const n
  | add _ _ ih1 ih2 => exact Primrec.nat_add.comp ih1 ih2
  | mul _ _ ih1 ih2 => exact Primrec.nat_mul.comp ih1 ih2

/-- Split an integer polynomial as a difference of two natural polynomials. -/
private theorem dp_isPoly_split {γ : Type} {f : (γ → ℕ) → ℤ} (hf : IsPoly f) :
    ∃ F G : (γ → ℕ) → ℕ,
      dpNatPoly F ∧ dpNatPoly G ∧ ∀ v, f v = (F v : ℤ) - (G v : ℤ) := by
  induction hf with
  | proj i =>
    exact ⟨_, _, .var i, .const 0, fun v => by simp⟩
  | const n =>
    refine ⟨fun _ => n.toNat, fun _ => (-n).toNat, .const _, .const _, fun v => by simp only; omega⟩
  | sub _ _ ih1 ih2 =>
    obtain ⟨F₁, G₁, hF₁, hG₁, e₁⟩ := ih1
    obtain ⟨F₂, G₂, hF₂, hG₂, e₂⟩ := ih2
    exact ⟨fun v => F₁ v + G₂ v, fun v => G₁ v + F₂ v,
      .add hF₁ hG₂, .add hG₁ hF₂, fun v => by simp only; rw [e₁ v, e₂ v]; push_cast; ring⟩
  | mul _ _ ih1 ih2 =>
    obtain ⟨F₁, G₁, hF₁, hG₁, e₁⟩ := ih1
    obtain ⟨F₂, G₂, hF₂, hG₂, e₂⟩ := ih2
    exact ⟨fun v => F₁ v * F₂ v + G₁ v * G₂ v, fun v => F₁ v * G₂ v + G₁ v * F₂ v,
      .add (.mul hF₁ hF₂) (.mul hG₁ hG₂), .add (.mul hF₁ hG₂) (.mul hG₁ hF₂),
      fun v => by simp only; rw [e₁ v, e₂ v]; push_cast; ring⟩

/-- Bound on `natAbs` from a split. -/
private theorem dp_isPoly_natAbs_le {γ : Type} {f : (γ → ℕ) → ℤ}
    {F G : (γ → ℕ) → ℕ}
    (heq : ∀ v, f v = (F v : ℤ) - (G v : ℤ)) (v : γ → ℕ) :
    (f v).natAbs ≤ F v + G v := by
  rw [heq v]
  have h1 : (-(G v : ℤ)) ≤ (G v : ℤ) := by
    have : (0 : ℤ) ≤ (G v : ℤ) := Int.natCast_nonneg _
    linarith
  have h2 : (-(F v : ℤ)) ≤ (F v : ℤ) := by
    have : (0 : ℤ) ≤ (F v : ℤ) := Int.natCast_nonneg _
    linarith
  have hle : |(F v : ℤ) - (G v : ℤ)| ≤ (F v : ℤ) + (G v : ℤ) := by
    rw [abs_le]
    constructor <;> linarith
  have hcast : ((F v + G v : ℕ) : ℤ) = (F v : ℤ) + (G v : ℤ) := by push_cast; ring
  have hle' : ((((F v : ℤ) - (G v : ℤ)).natAbs : ℕ) : ℤ) ≤ ((F v + G v : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs, hcast]
    exact hle
  exact Int.ofNat_le.mp hle'

/-- Integer polynomials respect pointwise `ZMOD` congruence. -/
private theorem dp_isPoly_modEq {γ : Type} {f : (γ → ℕ) → ℤ} (hf : IsPoly f)
    {m : ℤ} {v w : γ → ℕ} (hvw : ∀ i, (v i : ℤ) ≡ (w i : ℤ) [ZMOD m]) :
    f v ≡ f w [ZMOD m] := by
  induction hf with
  | proj i => exact hvw i
  | const n => exact rfl
  | sub _ _ ih1 ih2 => exact ih1.sub ih2
  | mul _ _ ih1 ih2 => exact ih1.mul ih2

/-- Every integer polynomial depends on finitely many variables. -/
private theorem dp_isPoly_support {γ : Type} {f : (γ → ℕ) → ℤ} (hf : IsPoly f) :
    ∃ s : Finset γ, ∀ {v w : γ → ℕ}, (∀ i ∈ s, v i = w i) → f v = f w := by
  classical
  induction hf with
  | proj i => exact ⟨{i}, fun h => by simp [h i (Finset.mem_singleton_self i)]⟩
  | const n => exact ⟨∅, fun _ => rfl⟩
  | sub _ _ ih1 ih2 =>
    obtain ⟨s₁, hs₁⟩ := ih1
    obtain ⟨s₂, hs₂⟩ := ih2
    exact ⟨s₁ ∪ s₂, fun h => by
      have h1 : ∀ i ∈ s₁, _ := fun i hi => h i (Finset.mem_union_left s₂ hi)
      have h2 : ∀ i ∈ s₂, _ := fun i hi => h i (Finset.mem_union_right s₁ hi)
      simp only
      rw [hs₁ h1, hs₂ h2]⟩
  | mul _ _ ih1 ih2 =>
    obtain ⟨s₁, hs₁⟩ := ih1
    obtain ⟨s₂, hs₂⟩ := ih2
    exact ⟨s₁ ∪ s₂, fun h => by
      have h1 : ∀ i ∈ s₁, _ := fun i hi => h i (Finset.mem_union_left s₂ hi)
      have h2 : ∀ i ∈ s₂, _ := fun i hi => h i (Finset.mem_union_right s₁ hi)
      simp only
      rw [hs₁ h1, hs₂ h2]⟩

/-- Normalize a Diophantine set to finitely many dummy variables. -/
private theorem dp_fin_dummies {α : Type} {S : Set (α → ℕ)} (hS : Dioph S) :
    ∃ m : ℕ, ∃ p : Poly (α ⊕ Fin m),
      ∀ v, v ∈ S ↔ ∃ t : Fin m → ℕ, p (Sum.elim v t) = 0 := by
  classical
  obtain ⟨β, p₀, hp₀⟩ := hS
  obtain ⟨s, hs⟩ := dp_isPoly_support p₀.isPoly
  let D : Finset β := s.preimage Sum.inr (Set.injOn_of_injective Sum.inr_injective)
  have hmem : ∀ b : β, b ∈ D ↔ Sum.inr b ∈ s := fun b => Finset.mem_preimage
  let e' : D ≃ Fin D.card := Fintype.equivFinOfCardEq (Fintype.card_coe D)
  let σ : α ⊕ β → α ⊕ Fin (D.card + 1) := fun x => match x with
    | Sum.inl a => Sum.inl a
    | Sum.inr b => if h : b ∈ D then Sum.inr (Fin.succ (e' ⟨b, h⟩)) else Sum.inr 0
  refine ⟨D.card + 1, p₀.map σ, fun v => ?_⟩
  rw [hp₀ v]
  constructor
  · rintro ⟨t₀, ht₀⟩
    let t : Fin (D.card + 1) → ℕ :=
      Fin.cons (α := fun _ => ℕ) 0 (fun j => t₀ ((e'.symm j).val))
    refine ⟨t, ?_⟩
    rw [Poly.map_apply]
    have hagree : ∀ i ∈ s, ((Sum.elim v t) ∘ σ) i = (Sum.elim v t₀) i := by
      intro i hi
      cases i with
      | inl a => rfl
      | inr b =>
        have hb : b ∈ D := (hmem b).mpr hi
        change (Sum.elim v t) (σ (Sum.inr b)) = t₀ b
        have hσ : σ (Sum.inr b) = Sum.inr (Fin.succ (e' ⟨b, hb⟩)) := by
          simp [σ, hb]
        rw [hσ]
        change t (Fin.succ (e' ⟨b, hb⟩)) = t₀ b
        change (Fin.cons (α := fun _ => ℕ) 0 (fun j => t₀ ((e'.symm j).val)))
          (Fin.succ _) = _
        rw [Fin.cons_succ]
        have h2 : e'.symm (e' ⟨b, hb⟩) = (⟨b, hb⟩ : D) :=
          Equiv.symm_apply_apply _ _
        have h3 : (e'.symm (e' ⟨b, hb⟩)).val = b := congrArg Subtype.val h2
        rw [h3]
    -- Use `hs` to transport the zero (`hs` needs agreement only on `s`)
    have hval : p₀ ((Sum.elim v t) ∘ σ) = p₀ (Sum.elim v t₀) :=
      hs hagree
    rw [hval, ht₀]
  · rintro ⟨t, ht⟩
    let t' : β → ℕ := fun b => if h : b ∈ D then t (Fin.succ (e' ⟨b, h⟩)) else t 0
    refine ⟨t', ?_⟩
    have hcomp : ((Sum.elim v t) ∘ σ) = Sum.elim v t' := by
      funext i
      cases i with
      | inl a => rfl
      | inr b =>
        change (Sum.elim v t) (σ (Sum.inr b)) = t' b
        by_cases hb : b ∈ D
        · have hσ : σ (Sum.inr b) = Sum.inr (Fin.succ (e' ⟨b, hb⟩)) := by
            simp [σ, hb]
          rw [hσ]
          simp [t', hb]
        · have hσ : σ (Sum.inr b) = Sum.inr 0 := by simp [σ, hb]
          rw [hσ]
          simp [t', hb]
    rw [Poly.map_apply] at ht
    rw [hcomp] at ht
    exact ht

/-- Graph of `Nat.pair` as a Diophantine set. -/
private theorem dp_pair_graph :
    Dioph {v : Vector3 ℕ 3 | Nat.pair (v &1) (v &2) = v &0} := by
  have hset : Dioph
      {v : Vector3 ℕ 3 |
        (v &1 < v &2 ∧ v &0 = v &2 * v &2 + v &1) ∨
        (v &2 ≤ v &1 ∧ v &0 = v &1 * v &1 + v &1 + v &2)} :=
    (D&1 D< D&2 D∧ D&0 D= D&2 D* D&2 D+ D&1) D∨
      (D&2 D≤ D&1 D∧ D&0 D= D&1 D* D&1 D+ D&1 D+ D&2)
  refine Dioph.ext hset fun v => ?_
  constructor
  · rintro (⟨hlt, heq⟩ | ⟨hle, heq⟩)
    · have hpair : Nat.pair (v &1) (v &2) = v &2 * v &2 + v &1 := by
        simp [Nat.pair, hlt]
      have hgoal : Nat.pair (v &1) (v &2) = v &0 := by rw [hpair, heq]
      exact hgoal
    · have hneg : ¬ v &1 < v &2 := Nat.not_lt.mpr hle
      have hpair : Nat.pair (v &1) (v &2) = v &1 * v &1 + v &1 + v &2 := by
        simp [Nat.pair, hneg]
      have hgoal : Nat.pair (v &1) (v &2) = v &0 := by rw [hpair, heq]
      exact hgoal
  · intro h
    have heq0 : Nat.pair (v &1) (v &2) = v &0 := h
    by_cases hlt : v &1 < v &2
    · left
      refine ⟨hlt, ?_⟩
      have hpair : Nat.pair (v &1) (v &2) = v &2 * v &2 + v &1 := by
        simp [Nat.pair, hlt]
      rw [hpair] at heq0
      exact heq0.symm
    · right
      have hle : v &2 ≤ v &1 := Nat.le_of_not_gt hlt
      refine ⟨hle, ?_⟩
      have hpair : Nat.pair (v &1) (v &2) = v &1 * v &1 + v &1 + v &2 := by
        simp [Nat.pair, hlt]
      rw [hpair] at heq0
      exact heq0.symm

/-- `Nat.pair` as a Diophantine function. -/
private theorem dp_pair_diophFn :
    Dioph.DiophFn (fun v : Vector3 ℕ 2 => Nat.pair (v &0) (v &1)) := by
  refine (Dioph.diophFn_vec _).2 (Dioph.ext dp_pair_graph fun v => Iff.rfl)

/-- First unpairing projection as a Diophantine function. -/
private theorem dp_unpair_fst_diophFn :
    Dioph.DiophFn (fun v : Vector3 ℕ 1 => (Nat.unpair (v &0)).1) := by
  have hS : Dioph {w : Vector3 ℕ 3 | Nat.pair (w &1) (w &0) = w &2} := by
    have hset : Dioph
        {w : Vector3 ℕ 3 |
          (w &1 < w &0 ∧ w &2 = w &0 * w &0 + w &1) ∨
          (w &0 ≤ w &1 ∧ w &2 = w &1 * w &1 + w &1 + w &0)} :=
      (D&1 D< D&0 D∧ D&2 D= D&0 D* D&0 D+ D&1) D∨
        (D&0 D≤ D&1 D∧ D&2 D= D&1 D* D&1 D+ D&1 D+ D&0)
    refine Dioph.ext hset fun w => ?_
    constructor
    · rintro (⟨hlt, heq⟩ | ⟨hle, heq⟩)
      · have hpair : Nat.pair (w &1) (w &0) = w &0 * w &0 + w &1 := by
          simp [Nat.pair, hlt]
        have hgoal : Nat.pair (w &1) (w &0) = w &2 := by rw [hpair, heq]
        exact hgoal
      · have hneg : ¬ w &1 < w &0 := Nat.not_lt.mpr hle
        have hpair : Nat.pair (w &1) (w &0) = w &1 * w &1 + w &1 + w &0 := by
          simp [Nat.pair, hneg]
        have hgoal : Nat.pair (w &1) (w &0) = w &2 := by rw [hpair, heq]
        exact hgoal
    · intro h
      have heq0 : Nat.pair (w &1) (w &0) = w &2 := h
      by_cases hlt : w &1 < w &0
      · left
        refine ⟨hlt, ?_⟩
        have hpair : Nat.pair (w &1) (w &0) = w &0 * w &0 + w &1 := by
          simp [Nat.pair, hlt]
        rw [hpair] at heq0
        exact heq0.symm
      · right
        have hle : w &0 ≤ w &1 := Nat.le_of_not_gt hlt
        refine ⟨hle, ?_⟩
        have hpair : Nat.pair (w &1) (w &0) = w &1 * w &1 + w &1 + w &0 := by
          simp [Nat.pair, hlt]
        rw [hpair] at heq0
        exact heq0.symm
  have hex : Dioph {v : Vector3 ℕ 2 | ∃ x, (x :: v) ∈
      {w : Vector3 ℕ 3 | Nat.pair (w &1) (w &0) = w &2}} :=
    Dioph.vec_ex1_dioph 2 hS
  refine (Dioph.diophFn_vec _).2 ?_
  refine Dioph.ext hex fun v => ?_
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, hz⟩
    have hz' : Nat.pair (v &0) z = v &1 := hz
    have hup := Nat.unpair_pair (v &0) z
    rw [hz'] at hup
    have e1 : ((v ∘ Fin2.fs) &0) = v &1 := rfl
    have e0 : v Fin2.fz = v &0 := rfl
    rw [e1, e0]
    have hgoal : (Nat.unpair (v &1)).1 = v &0 := by rw [hup]
    exact hgoal
  · intro h
    have e1 : ((v ∘ Fin2.fs) &0) = v &1 := rfl
    have e0 : v Fin2.fz = v &0 := rfl
    rw [e1, e0] at h
    refine ⟨(Nat.unpair (v &1)).2, ?_⟩
    have hpu := Nat.pair_unpair (v &1)
    have hgoal : Nat.pair (v &0) (Nat.unpair (v &1)).2 = v &1 := by
      conv_lhs => rw [← h]
      exact hpu
    exact hgoal

/-- Extracting a base-`u` digit via division and modulus. -/
private theorem dp_digit_main (u : ℕ) (hu : 2 ≤ u) (N : ℕ) (d : ℕ → ℕ)
    (hd : ∀ i < N, d i < u) (k : ℕ) :
    (∑ i ∈ Finset.range N, d i * u ^ i) / u ^ k % u
      = if k < N then d k else 0 := by
  induction k generalizing N d with
  | zero =>
    cases N with
    | zero => simp
    | succ N' =>
      have h0 : d 0 < u := hd 0 (Nat.zero_lt_succ N')
      have hT : (∑ i ∈ Finset.range N', d (i + 1) * u ^ (i + 1))
          = u * (∑ i ∈ Finset.range N', d (i + 1) * u ^ i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [pow_succ']
        ring
      have hsum : (∑ i ∈ Finset.range (N' + 1), d i * u ^ i)
          = d 0 + u * (∑ i ∈ Finset.range N', d (i + 1) * u ^ i) := by
        have h1 : (∑ i ∈ Finset.range (N' + 1), d i * u ^ i)
            = (∑ i ∈ Finset.range N', d (i + 1) * u ^ (i + 1)) + d 0 := by
          rw [Finset.sum_range_succ']
          simp only [pow_zero, mul_one]
        rw [h1, hT]
        exact add_comm _ _
      rw [pow_zero, Nat.div_one]
      rw [hsum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
      simp
  | succ k ih =>
    cases N with
    | zero => simp
    | succ N' =>
      have hu0 : 0 < u := by omega
      have h0 : d 0 < u := hd 0 (Nat.zero_lt_succ N')
      have hT : (∑ i ∈ Finset.range N', d (i + 1) * u ^ (i + 1))
          = u * (∑ i ∈ Finset.range N', d (i + 1) * u ^ i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [pow_succ']
        ring
      have hsum : (∑ i ∈ Finset.range (N' + 1), d i * u ^ i)
          = d 0 + u * (∑ i ∈ Finset.range N', d (i + 1) * u ^ i) := by
        have h1 : (∑ i ∈ Finset.range (N' + 1), d i * u ^ i)
            = (∑ i ∈ Finset.range N', d (i + 1) * u ^ (i + 1)) + d 0 := by
          rw [Finset.sum_range_succ']
          simp only [pow_zero, mul_one]
        rw [h1, hT]
        exact add_comm _ _
      have hdiv : (∑ i ∈ Finset.range (N' + 1), d i * u ^ i) / u
          = ∑ i ∈ Finset.range N', d (i + 1) * u ^ i := by
        rw [hsum, Nat.add_mul_div_left _ _ hu0, Nat.div_eq_of_lt h0, Nat.zero_add]
      have hdk : ∀ i < N', d (i + 1) < u := fun i hi =>
        hd (i + 1) (Nat.succ_lt_succ hi)
      have hstep : (∑ i ∈ Finset.range (N' + 1), d i * u ^ i) / u ^ (k + 1)
          = (∑ i ∈ Finset.range N', d (i + 1) * u ^ i) / u ^ k := by
        rw [pow_succ, Nat.mul_comm (u ^ k) u, ← Nat.div_div_eq_div_mul, hdiv]
      rw [hstep, ih _ _ hdk]
      by_cases hk : k < N'
      · have hk' : k + 1 < N' + 1 := Nat.succ_lt_succ hk
        simp [hk, hk']
      · have hk' : ¬ k + 1 < N' + 1 := by omega
        simp [hk, hk']

/-- Binomial coefficient via base-`u` digits. -/
private theorem dp_choose_eq (n k : ℕ) :
    n.choose k = (((2 ^ n + 1 + 1) ^ n / (2 ^ n + 1) ^ k) % (2 ^ n + 1)) := by
  set u := 2 ^ n + 1 with hu_def
  have h2n : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  have hu : 2 ≤ u := by simp only [hu_def]; omega
  have hdigit : ∀ i < n + 1, n.choose i < u := by
    intro i _
    calc n.choose i ≤ 2 ^ n := Nat.choose_le_two_pow n i
      _ < 2 ^ n + 1 := Nat.lt_succ_self _
      _ = u := rfl
  have hpow : (u + 1) ^ n
      = ∑ i ∈ Finset.range (n + 1), n.choose i * u ^ i := by
    have h := add_pow u 1 n
    simp only [mul_one, one_pow] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  rw [hpow]
  rw [dp_digit_main u hu (n + 1) (fun i => n.choose i) hdigit k]
  by_cases hk : k < n + 1
  · simp [hk]
  · have hk' : n < k := by omega
    have h0 : n.choose k = 0 := Nat.choose_eq_zero_of_lt hk'
    simp [hk, h0]

/-- Binomial coefficient as a Diophantine function. -/
private theorem dp_choose_diophFn :
    Dioph.DiophFn (fun v : Vector3 ℕ 2 => (v &0).choose (v &1)) := by
  have hn : Dioph.DiophFn (fun v : Vector3 ℕ 2 => v &0) := Dioph.proj_dioph_of_nat 0
  have hk : Dioph.DiophFn (fun v : Vector3 ℕ 2 => v &1) := Dioph.proj_dioph_of_nat 1
  have hc1 : Dioph.DiophFn (fun _ : Vector3 ℕ 2 => (1 : ℕ)) := Dioph.const_dioph 1
  have hc2 : Dioph.DiophFn (fun _ : Vector3 ℕ 2 => (2 : ℕ)) := Dioph.const_dioph 2
  have hpow2n : Dioph.DiophFn (fun v : Vector3 ℕ 2 => 2 ^ v &0) :=
    Dioph.pow_dioph hc2 hn
  have hu : Dioph.DiophFn (fun v : Vector3 ℕ 2 => 2 ^ v &0 + 1) :=
    Dioph.add_dioph hpow2n hc1
  have hu1 : Dioph.DiophFn (fun v : Vector3 ℕ 2 => 2 ^ v &0 + 1 + 1) :=
    Dioph.add_dioph hu hc1
  have hpow1 : Dioph.DiophFn (fun v : Vector3 ℕ 2 => (2 ^ v &0 + 1 + 1) ^ v &0) :=
    Dioph.pow_dioph hu1 hn
  have hpow2 : Dioph.DiophFn (fun v : Vector3 ℕ 2 => (2 ^ v &0 + 1) ^ v &1) :=
    Dioph.pow_dioph hu hk
  have hdiv : Dioph.DiophFn
      (fun v : Vector3 ℕ 2 => (2 ^ v &0 + 1 + 1) ^ v &0 / (2 ^ v &0 + 1) ^ v &1) :=
    Dioph.div_dioph hpow1 hpow2
  have hmod : Dioph.DiophFn
      (fun v : Vector3 ℕ 2 =>
        ((2 ^ v &0 + 1 + 1) ^ v &0 / (2 ^ v &0 + 1) ^ v &1) % (2 ^ v &0 + 1)) :=
    Dioph.mod_dioph hdiv hu
  have hfun : (fun v : Vector3 ℕ 2 => (v &0).choose (v &1))
      = (fun v : Vector3 ℕ 2 =>
        ((2 ^ v &0 + 1 + 1) ^ v &0 / (2 ^ v &0 + 1) ^ v &1) % (2 ^ v &0 + 1)) := by
    funext v
    exact dp_choose_eq (v &0) (v &1)
  exact hfun ▸ hmod

/-- Second unpairing projection as a Diophantine function. -/
private theorem dp_unpair_snd_diophFn :
    Dioph.DiophFn (fun v : Vector3 ℕ 1 => (Nat.unpair (v &0)).2) := by
  have hS : Dioph {w : Vector3 ℕ 3 | Nat.pair (w &0) (w &1) = w &2} := by
    have hset : Dioph
        {w : Vector3 ℕ 3 |
          (w &0 < w &1 ∧ w &2 = w &1 * w &1 + w &0) ∨
          (w &1 ≤ w &0 ∧ w &2 = w &0 * w &0 + w &0 + w &1)} :=
      (D&0 D< D&1 D∧ D&2 D= D&1 D* D&1 D+ D&0) D∨
        (D&1 D≤ D&0 D∧ D&2 D= D&0 D* D&0 D+ D&0 D+ D&1)
    refine Dioph.ext hset fun w => ?_
    constructor
    · rintro (⟨hlt, heq⟩ | ⟨hle, heq⟩)
      · have hpair : Nat.pair (w &0) (w &1) = w &1 * w &1 + w &0 := by
          simp [Nat.pair, hlt]
        have hgoal : Nat.pair (w &0) (w &1) = w &2 := by rw [hpair, heq]
        exact hgoal
      · have hneg : ¬ w &0 < w &1 := Nat.not_lt.mpr hle
        have hpair : Nat.pair (w &0) (w &1) = w &0 * w &0 + w &0 + w &1 := by
          simp [Nat.pair, hneg]
        have hgoal : Nat.pair (w &0) (w &1) = w &2 := by rw [hpair, heq]
        exact hgoal
    · intro h
      have heq0 : Nat.pair (w &0) (w &1) = w &2 := h
      by_cases hlt : w &0 < w &1
      · left
        refine ⟨hlt, ?_⟩
        have hpair : Nat.pair (w &0) (w &1) = w &1 * w &1 + w &0 := by
          simp [Nat.pair, hlt]
        rw [hpair] at heq0
        exact heq0.symm
      · right
        have hle : w &1 ≤ w &0 := Nat.le_of_not_gt hlt
        refine ⟨hle, ?_⟩
        have hpair : Nat.pair (w &0) (w &1) = w &0 * w &0 + w &0 + w &1 := by
          simp [Nat.pair, hlt]
        rw [hpair] at heq0
        exact heq0.symm
  have hex : Dioph {v : Vector3 ℕ 2 | ∃ x, (x :: v) ∈
      {w : Vector3 ℕ 3 | Nat.pair (w &0) (w &1) = w &2}} :=
    Dioph.vec_ex1_dioph 2 hS
  refine (Dioph.diophFn_vec _).2 ?_
  refine Dioph.ext hex fun v => ?_
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, hz⟩
    have hz' : Nat.pair z (v &0) = v &1 := hz
    have hup := Nat.unpair_pair z (v &0)
    rw [hz'] at hup
    have e1 : ((v ∘ Fin2.fs) &0) = v &1 := rfl
    have e0 : v Fin2.fz = v &0 := rfl
    rw [e1, e0]
    have hgoal : (Nat.unpair (v &1)).2 = v &0 := by rw [hup]
    exact hgoal
  · intro h
    have e1 : ((v ∘ Fin2.fs) &0) = v &1 := rfl
    have e0 : v Fin2.fz = v &0 := rfl
    rw [e1, e0] at h
    refine ⟨(Nat.unpair (v &1)).1, ?_⟩
    have hpu := Nat.pair_unpair (v &1)
    have hgoal : Nat.pair (Nat.unpair (v &1)).1 (v &0) = v &1 := by
      conv_lhs => rw [← h]
      exact hpu
    exact hgoal

/-- Power difference bound (avoids truncated exponents). -/
private theorem dp_pow_le (a b n : ℕ) (h : b ≤ a) :
    a ^ (n + 1) ≤ b ^ (n + 1) + (n + 1) * (a - b) * a ^ n := by
  induction n with
  | zero =>
    simp only [Nat.zero_add, pow_one, pow_zero, mul_one, one_mul]
    omega
  | succ n ih =>
    have hb : b ^ (n + 1) ≤ a ^ (n + 1) := Nat.pow_le_pow_left h _
    have hba : b + (a - b) = a := Nat.add_sub_cancel' h
    have e1 : a ^ (n + 2) = a * a ^ (n + 1) := by rw [pow_succ']
    have e2 : b ^ (n + 2) = b * b ^ (n + 1) := by rw [pow_succ']
    have s1 : a * a ^ (n + 1)
        ≤ a * (b ^ (n + 1) + (n + 1) * (a - b) * a ^ n) :=
      Nat.mul_le_mul_left _ ih
    have s1' : a * (b ^ (n + 1) + (n + 1) * (a - b) * a ^ n)
        = a * b ^ (n + 1) + (n + 1) * (a - b) * a ^ (n + 1) := by
      have hpow : a * a ^ n = a ^ (n + 1) := by rw [pow_succ']
      have : a * ((n + 1) * (a - b) * a ^ n)
          = (n + 1) * (a - b) * a ^ (n + 1) := by
        rw [pow_succ']; ring
      rw [Nat.mul_add, this]
    have s2 : a * b ^ (n + 1)
        ≤ b ^ (n + 2) + (a - b) * a ^ (n + 1) := by
      have ha : a * b ^ (n + 1)
          = b * b ^ (n + 1) + (a - b) * b ^ (n + 1) := by
        conv_lhs => rw [← hba]
        rw [Nat.add_mul]
      rw [ha, e2]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hb) _
    rw [e1]
    calc a * a ^ (n + 1)
        ≤ a * (b ^ (n + 1) + (n + 1) * (a - b) * a ^ n) := s1
      _ = a * b ^ (n + 1) + (n + 1) * (a - b) * a ^ (n + 1) := s1'
      _ ≤ (b ^ (n + 2) + (a - b) * a ^ (n + 1))
          + (n + 1) * (a - b) * a ^ (n + 1) :=
          Nat.add_le_add_right s2 _
      _ = b ^ (n + 2) + (n + 2) * (a - b) * a ^ (n + 1) := by ring

/-- Factorial via power divided by binomial. -/
private theorem dp_factorial_eq (n : ℕ) :
    (n)! = ((2 * n) ^ (n + 2) + 1) ^ n / (((2 * n) ^ (n + 2) + 1).choose n) := by
  cases n with
  | zero => simp
  | succ m =>
    set r := (2 * (m + 1)) ^ ((m + 1) + 2) + 1 with hr_def
    set F := r.descFactorial (m + 1) with hF_def
    have hm1 : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
    have h2m : (1 : ℕ) ≤ 2 * (m + 1) := by omega
    have hbase : 2 * (m + 1) ≤ (2 * (m + 1)) ^ ((m + 1) + 2) :=
      le_self_pow₀ h2m (by omega)
    have hr2 : 2 * (m + 1) ≤ r := by simp only [hr_def]; omega
    have hrn : m + 1 ≤ r := by omega
    have hX : (2 * (m + 1)) ^ ((m + 1) + 2) < r := by simp [hr_def]
    have hF : F = (m + 1)! * r.choose (m + 1) :=
      Nat.descFactorial_eq_factorial_mul_choose r (m + 1)
    have hFle : F ≤ r ^ (m + 1) := Nat.descFactorial_le_pow r (m + 1)
    have hle1 : (m + 1)! * r.choose (m + 1) ≤ r ^ (m + 1) := by
      rw [← hF]; exact hFle
    have hFlow : (r - (m + 1)) ^ (m + 1) ≤ F := by
      have h1 : (r + 1 - (m + 1)) ^ (m + 1) ≤ F :=
        Nat.pow_sub_le_descFactorial r (m + 1)
      have h2 : (r - (m + 1)) ^ (m + 1) ≤ (r + 1 - (m + 1)) ^ (m + 1) := by
        apply Nat.pow_le_pow_left
        omega
      exact le_trans h2 h1
    have hrr : r - (r - (m + 1)) = m + 1 := by omega
    have hple := dp_pow_le r (r - (m + 1)) m (by omega)
    rw [hrr] at hple
    have hgap : r ^ (m + 1) - F
        ≤ (m + 1) * (m + 1) * r ^ m := by
      have hmem : r ^ (m + 1)
          ≤ (r - (m + 1)) ^ (m + 1) + (m + 1) * (m + 1) * r ^ m := hple
      have hle : (r - (m + 1)) ^ (m + 1) ≤ F := hFlow
      omega
    have h2sub : 2 * (r - (m + 1)) ≥ r := by omega
    have h2n : 2 ^ (m + 1) * (r - (m + 1)) ^ (m + 1) ≥ r ^ (m + 1) := by
      have hle : (2 * (r - (m + 1))) ^ (m + 1) ≥ r ^ (m + 1) :=
        Nat.pow_le_pow_left h2sub _
      rw [mul_pow] at hle
      exact hle
    have hfact : (m + 1)! ≤ (m + 1) ^ (m + 1) := Nat.factorial_le_pow _
    have hpos2 : 0 < 2 ^ (m + 1) := by positivity
    have hposF : 0 < (m + 1)! := Nat.factorial_pos _
    have hmain : (m + 1)! * (r ^ (m + 1) - F) * 2 ^ (m + 1)
        < 2 ^ (m + 1) * F := by
      have e1 : (m + 1)! * (r ^ (m + 1) - F) * 2 ^ (m + 1)
          ≤ (m + 1)! * ((m + 1) * (m + 1) * r ^ m) * 2 ^ (m + 1) := by
        apply Nat.mul_le_mul_right
        apply Nat.mul_le_mul_left
        exact hgap
      have e2 : (m + 1)! * ((m + 1) * (m + 1) * r ^ m) * 2 ^ (m + 1)
          = ((m + 1)! * (m + 1) ^ 2 * 2 ^ (m + 1)) * r ^ m := by
        ring
      have e3 : (m + 1)! * (m + 1) ^ 2 * 2 ^ (m + 1)
          ≤ (2 * (m + 1)) ^ ((m + 1) + 2) := by
        have hAC : (m + 1)! ≤ (m + 1) ^ (m + 1) * 4 := by
          calc (m + 1)! ≤ (m + 1) ^ (m + 1) := hfact
            _ = (m + 1) ^ (m + 1) * 1 := by ring
            _ ≤ (m + 1) ^ (m + 1) * 4 :=
                Nat.mul_le_mul_left _ (by norm_num)
        have hR : (2 * (m + 1)) ^ ((m + 1) + 2)
            = ((m + 1) ^ (m + 1) * 4) * ((m + 1) ^ 2 * 2 ^ (m + 1)) := by
          rw [mul_pow]
          ring
        have hL : (m + 1)! * (m + 1) ^ 2 * 2 ^ (m + 1)
            = (m + 1)! * ((m + 1) ^ 2 * 2 ^ (m + 1)) := by ring
        rw [hL, hR]
        exact Nat.mul_le_mul hAC le_rfl
      have hXr : (m + 1)! * (m + 1) ^ 2 * 2 ^ (m + 1) < r := by
        calc (m + 1)! * (m + 1) ^ 2 * 2 ^ (m + 1)
              ≤ (2 * (m + 1)) ^ ((m + 1) + 2) := e3
            _ < r := hX
      have e4 : ((m + 1)! * (m + 1) ^ 2 * 2 ^ (m + 1)) * r ^ m
          < r * r ^ m :=
        (Nat.mul_lt_mul_right (pow_pos (by omega : 0 < r) m)).mpr hXr
      have e5 : r * r ^ m = r ^ (m + 1) := by rw [pow_succ']
      have e6 : r ^ (m + 1) ≤ 2 ^ (m + 1) * (r - (m + 1)) ^ (m + 1) := h2n
      have e7 : 2 ^ (m + 1) * (r - (m + 1)) ^ (m + 1)
          ≤ 2 ^ (m + 1) * F :=
        Nat.mul_le_mul_left _ hFlow
      calc (m + 1)! * (r ^ (m + 1) - F) * 2 ^ (m + 1)
          ≤ (m + 1)! * ((m + 1) * (m + 1) * r ^ m) * 2 ^ (m + 1) := e1
        _ = ((m + 1)! * (m + 1) ^ 2 * 2 ^ (m + 1)) * r ^ m := e2
        _ < r * r ^ m := e4
        _ = r ^ (m + 1) := e5
        _ ≤ 2 ^ (m + 1) * (r - (m + 1)) ^ (m + 1) := e6
        _ ≤ 2 ^ (m + 1) * F := e7
    have hkey : (m + 1)! * (r ^ (m + 1) - F) < F := by
      have hmain' : (m + 1)! * (r ^ (m + 1) - F) * 2 ^ (m + 1)
          < F * 2 ^ (m + 1) := by
        have hrw : 2 ^ (m + 1) * F = F * 2 ^ (m + 1) := by ring
        rwa [hrw] at hmain
      exact (Nat.mul_lt_mul_right hpos2).mp hmain'
    have hC : r ^ (m + 1) - F < r.choose (m + 1) := by
      have hmul : (m + 1)! * (r ^ (m + 1) - F) < (m + 1)! * r.choose (m + 1) := by
        rw [← hF]; exact hkey
      exact (Nat.mul_lt_mul_left hposF).mp hmul
    have hlt2 : r ^ (m + 1) < ((m + 1)! + 1) * r.choose (m + 1) := by
      have hdecomp : r ^ (m + 1) = F + (r ^ (m + 1) - F) := by
        have : F ≤ r ^ (m + 1) := hFle
        omega
      have hF2 : F + (r ^ (m + 1) - F) < F + r.choose (m + 1) :=
        Nat.add_lt_add_left hC _
      have hexpand : ((m + 1)! + 1) * r.choose (m + 1)
          = F + r.choose (m + 1) := by
        rw [hF]; ring
      omega
    have hdiv := Nat.div_eq_of_lt_le hle1 hlt2
    exact hdiv.symm

/-- Factorial as a Diophantine function. -/
private theorem dp_factorial_diophFn :
    Dioph.DiophFn (fun v : Vector3 ℕ 1 => (v &0)!) := by
  have hn : Dioph.DiophFn (fun v : Vector3 ℕ 1 => v &0) := Dioph.proj_dioph_of_nat 0
  have hc1 : Dioph.DiophFn (fun _ : Vector3 ℕ 1 => (1 : ℕ)) := Dioph.const_dioph 1
  have hc2 : Dioph.DiophFn (fun _ : Vector3 ℕ 1 => (2 : ℕ)) := Dioph.const_dioph 2
  have h2n : Dioph.DiophFn (fun v : Vector3 ℕ 1 => 2 * v &0) :=
    Dioph.mul_dioph hc2 hn
  have hn2 : Dioph.DiophFn (fun v : Vector3 ℕ 1 => v &0 + 2) :=
    Dioph.add_dioph hn (Dioph.const_dioph 2)
  have hrpow : Dioph.DiophFn (fun v : Vector3 ℕ 1 => (2 * v &0) ^ (v &0 + 2)) :=
    Dioph.pow_dioph h2n hn2
  have hr : Dioph.DiophFn (fun v : Vector3 ℕ 1 => (2 * v &0) ^ (v &0 + 2) + 1) :=
    Dioph.add_dioph hrpow hc1
  have hpow1 : Dioph.DiophFn
      (fun v : Vector3 ℕ 1 => ((2 * v &0) ^ (v &0 + 2) + 1) ^ v &0) :=
    Dioph.pow_dioph hr hn
  have hchoose : Dioph.DiophFn
      (fun v : Vector3 ℕ 1 => ((2 * v &0) ^ (v &0 + 2) + 1).choose (v &0)) :=
    Dioph.diophFn_comp dp_choose_diophFn
      [(fun v : Vector3 ℕ 1 => (2 * v &0) ^ (v &0 + 2) + 1),
       (fun v : Vector3 ℕ 1 => v &0)]
      ⟨hr, hn⟩
  have hdiv : Dioph.DiophFn
      (fun v : Vector3 ℕ 1 =>
        ((2 * v &0) ^ (v &0 + 2) + 1) ^ v &0
          / ((2 * v &0) ^ (v &0 + 2) + 1).choose (v &0)) :=
    Dioph.div_dioph hpow1 hchoose
  have hfun : (fun v : Vector3 ℕ 1 => (v &0)!)
      = (fun v : Vector3 ℕ 1 =>
        ((2 * v &0) ^ (v &0 + 2) + 1) ^ v &0
          / ((2 * v &0) ^ (v &0 + 2) + 1).choose (v &0)) := by
    funext v
    exact dp_factorial_eq (v &0)
  exact hfun ▸ hdiv

/-- Descending factorial as a Diophantine function. -/
private theorem dp_descFactorial_diophFn :
    Dioph.DiophFn (fun v : Vector3 ℕ 2 => (v &0).descFactorial (v &1)) := by
  have h1 : Dioph.DiophFn (fun v : Vector3 ℕ 2 => v &1) :=
    Dioph.proj_dioph_of_nat 1
  have hfact : Dioph.DiophFn (fun v : Vector3 ℕ 2 => (v &1)!) :=
    Dioph.diophFn_comp dp_factorial_diophFn [(fun v : Vector3 ℕ 2 => v &1)] h1
  have hmul := Dioph.mul_dioph hfact dp_choose_diophFn
  have hfun : (fun v : Vector3 ℕ 2 => (v &0).descFactorial (v &1))
      = (fun v : Vector3 ℕ 2 => (v &1)! * (v &0).choose (v &1)) := by
    funext v
    exact Nat.descFactorial_eq_factorial_mul_choose (v &0) (v &1)
  exact hfun ▸ hmul

/-- Gödel's β function as a Diophantine function. -/
private theorem dp_beta_diophFn :
    Dioph.DiophFn (fun v : Vector3 ℕ 2 => Nat.beta (v &0) (v &1)) := by
  have h0 : Dioph.DiophFn (fun v : Vector3 ℕ 2 => v &0) :=
    Dioph.proj_dioph_of_nat 0
  have h1 : Dioph.DiophFn (fun v : Vector3 ℕ 2 => v &1) :=
    Dioph.proj_dioph_of_nat 1
  have hu1 : Dioph.DiophFn (fun v : Vector3 ℕ 2 => (Nat.unpair (v &0)).1) :=
    Dioph.diophFn_comp dp_unpair_fst_diophFn [(fun v : Vector3 ℕ 2 => v &0)] h0
  have hu2 : Dioph.DiophFn (fun v : Vector3 ℕ 2 => (Nat.unpair (v &0)).2) :=
    Dioph.diophFn_comp dp_unpair_snd_diophFn [(fun v : Vector3 ℕ 2 => v &0)] h0
  have hc1 : Dioph.DiophFn (fun _ : Vector3 ℕ 2 => (1 : ℕ)) := Dioph.const_dioph 1
  have hi1 : Dioph.DiophFn (fun v : Vector3 ℕ 2 => v &1 + 1) :=
    Dioph.add_dioph h1 hc1
  have hden : Dioph.DiophFn (fun v : Vector3 ℕ 2 => (v &1 + 1) * (Nat.unpair (v &0)).2 + 1) :=
    Dioph.add_dioph (Dioph.mul_dioph hi1 hu2) hc1
  have hmod : Dioph.DiophFn
      (fun v : Vector3 ℕ 2 => (Nat.unpair (v &0)).1 % ((v &1 + 1) * (Nat.unpair (v &0)).2 + 1)) :=
    Dioph.mod_dioph hu1 hden
  have hfun : (fun v : Vector3 ℕ 2 => Nat.beta (v &0) (v &1))
      = (fun v : Vector3 ℕ 2 =>
        (Nat.unpair (v &0)).1 % ((v &1 + 1) * (Nat.unpair (v &0)).2 + 1)) := by
    funext v
    simp [Nat.beta]
  exact hfun ▸ hmod

/-- Every list is coded by some β-code. -/
private theorem dp_beta_exists (l : List ℕ) :
    ∃ c, ∀ (i : ℕ) (h : i < l.length), Nat.beta c i = l[i] := by
  refine ⟨Nat.unbeta l, fun i hi => ?_⟩
  have := Nat.beta_unbeta_coe l ⟨i, hi⟩
  simpa using this

/-- Modulus for the product trick: `N = t * (1 + x * t) ^ x + 1`. -/
private def dpProdN (x t : ℕ) : ℕ := t * (1 + x * t) ^ x + 1

/-- The product `Π_{j<x} (1 + (j+1) * t)`. -/
private def dpProdP (x t : ℕ) : ℕ :=
  ∏ j ∈ Finset.range x, (1 + (j + 1) * t)

/-- Each factor is bounded by `1 + x * t`. -/
private theorem dp_prod_le (x t : ℕ) :
    dpProdP x t ≤ (1 + x * t) ^ x := by
  have hbound : ∀ j ∈ Finset.range x, (1 + (j + 1) * t) ≤ 1 + x * t := by
    intro j hj
    have hjx : j + 1 ≤ x := by
      have := Finset.mem_range.mp hj
      omega
    have hle : (j + 1) * t ≤ x * t := Nat.mul_le_mul_right t hjx
    omega
  have hmain := Finset.prod_le_pow_card (Finset.range x)
    (fun j => 1 + (j + 1) * t) (1 + x * t) hbound
  rw [Finset.card_range] at hmain
  unfold dpProdP
  exact hmain

/-- The product is below the modulus. -/
private theorem dp_prod_lt (x t : ℕ) (ht : 1 ≤ t) :
    dpProdP x t < dpProdN x t := by
  have hle := dp_prod_le x t
  have hK : 1 ≤ (1 + x * t) ^ x := Nat.one_le_pow x (1 + x * t) (by omega)
  unfold dpProdN
  calc dpProdP x t ≤ (1 + x * t) ^ x := hle
    _ < t * (1 + x * t) ^ x + 1 := by
        have : (1 + x * t) ^ x ≤ t * (1 + x * t) ^ x := by
          calc (1 + x * t) ^ x = 1 * (1 + x * t) ^ x := by ring
            _ ≤ t * (1 + x * t) ^ x := Nat.mul_le_mul_right _ ht
        omega

/-- Pointwise congruence lifts to products. -/
private theorem dp_modEq_prod (N x : ℕ) (f g : ℕ → ℕ)
    (h : ∀ j ∈ Finset.range x, f j ≡ g j [MOD N]) :
    (∏ j ∈ Finset.range x, f j) ≡ (∏ j ∈ Finset.range x, g j) [MOD N] := by
  induction x with
  | zero => rfl
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    exact Nat.ModEq.mul
      (ih fun j hj => h j (Finset.mem_range.mpr (lt_of_lt_of_le
        (Finset.mem_range.mp hj) (Nat.le_succ n))))
      (h n (Finset.mem_range.mpr (Nat.lt_succ_self n)))

/-- Key congruence for the product trick. -/
private theorem dp_prod_key (x t q : ℕ)
    (hq : t * q ≡ 1 [MOD dpProdN x t]) :
    t ^ x * ((x)! * (q + x).choose x) ≡ dpProdP x t [MOD dpProdN x t] := by
  have hasc : (x)! * (q + x).choose x = (q + 1).ascFactorial x :=
    (Nat.ascFactorial_eq_factorial_mul_choose q x).symm
  have hprod : (q + 1).ascFactorial x = ∏ j ∈ Finset.range x, (q + 1 + j) :=
    Nat.ascFactorial_eq_prod_range (q + 1) x
  have htx : t ^ x = ∏ _j ∈ Finset.range x, t := by
    rw [Finset.prod_const, Finset.card_range]
  have hLHS : t ^ x * ((x)! * (q + x).choose x)
      = ∏ j ∈ Finset.range x, (t * q + (j + 1) * t) := by
    rw [hasc, hprod, htx, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    ring
  rw [hLHS]
  unfold dpProdP
  apply dp_modEq_prod
  intro j _
  exact Nat.ModEq.add_right _ hq

/-- `t` is coprime to the modulus, giving the inverse `q`. -/
private theorem dp_prod_has_inv (x t : ℕ) (ht : 1 ≤ t) :
    ∃ q, t * q % dpProdN x t = 1 := by
  have hNpos : 1 < dpProdN x t := by
    unfold dpProdN
    have hKpos : 0 < (1 + x * t) ^ x := pow_pos (by omega) x
    have hle : 1 ≤ t * (1 + x * t) ^ x := by
      calc (1 : ℕ) = 1 * 1 := by ring
        _ ≤ t * (1 + x * t) ^ x := Nat.mul_le_mul ht hKpos
    omega
  have hcop : Nat.Coprime t (dpProdN x t) := by
    have h1 : dpProdN x t = 1 + (1 + x * t) ^ x * t := by
      unfold dpProdN; ring
    rw [h1, Nat.coprime_comm]
    exact (Nat.coprime_add_mul_right_left 1 t ((1 + x * t) ^ x)).mpr
      (Nat.coprime_one_left t)
  obtain ⟨q, _, hq⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hNpos
  exact ⟨q, hq⟩

/-- Characterization of the product via a modular inverse. -/
private theorem dp_prod_iff (x t z : ℕ) (ht : 1 ≤ t) :
    (z = dpProdP x t ↔ ∃ q, t * q ≡ 1 [MOD dpProdN x t] ∧
      z = (t ^ x * ((x)! * (q + x).choose x)) % dpProdN x t) := by
  have hN1 : 1 < dpProdN x t := by
    unfold dpProdN
    have hKpos : 0 < (1 + x * t) ^ x := pow_pos (by omega) x
    have hle : 1 ≤ t * (1 + x * t) ^ x := by
      calc (1 : ℕ) = 1 * 1 := by ring
        _ ≤ t * (1 + x * t) ^ x := Nat.mul_le_mul ht hKpos
    omega
  have hP : dpProdP x t % dpProdN x t = dpProdP x t :=
    Nat.mod_eq_of_lt (dp_prod_lt x t ht)
  constructor
  · intro hz
    obtain ⟨q, hq⟩ := dp_prod_has_inv x t ht
    have hmod : t * q ≡ 1 [MOD dpProdN x t] := by
      simp only [Nat.ModEq, hq, Nat.mod_eq_of_lt hN1]
    have hkey : (t ^ x * ((x)! * (q + x).choose x)) % dpProdN x t
        = dpProdP x t % dpProdN x t :=
      dp_prod_key x t q hmod
    exact ⟨q, hmod, by rw [hz, hkey, hP]⟩
  · rintro ⟨q, hq, hz⟩
    have hkey : (t ^ x * ((x)! * (q + x).choose x)) % dpProdN x t
        = dpProdP x t % dpProdN x t :=
      dp_prod_key x t q hq
    rw [hz, hkey, hP]

/-- The modulus as a Diophantine function of `(x, t)`. -/
private theorem dp_prodN_diophFn :
    Dioph.DiophFn (fun w : Vector3 ℕ 4 => dpProdN (w &2) (w &3)) := by
  have hx : Dioph.DiophFn (fun w : Vector3 ℕ 4 => w &2) :=
    Dioph.proj_dioph_of_nat 2
  have ht : Dioph.DiophFn (fun w : Vector3 ℕ 4 => w &3) :=
    Dioph.proj_dioph_of_nat 3
  have hc1 : Dioph.DiophFn (fun _ : Vector3 ℕ 4 => (1 : ℕ)) := Dioph.const_dioph 1
  have hxt : Dioph.DiophFn (fun w : Vector3 ℕ 4 => w &2 * w &3) :=
    Dioph.mul_dioph hx ht
  have h1xt : Dioph.DiophFn (fun w : Vector3 ℕ 4 => 1 + w &2 * w &3) :=
    Dioph.add_dioph hc1 hxt
  have hpw : Dioph.DiophFn (fun w : Vector3 ℕ 4 => (1 + w &2 * w &3) ^ w &2) :=
    Dioph.pow_dioph h1xt hx
  have htpw : Dioph.DiophFn (fun w : Vector3 ℕ 4 => w &3 * (1 + w &2 * w &3) ^ w &2) :=
    Dioph.mul_dioph ht hpw
  have hN : Dioph.DiophFn
      (fun w : Vector3 ℕ 4 => w &3 * (1 + w &2 * w &3) ^ w &2 + 1) :=
    Dioph.add_dioph htpw hc1
  have hfun : (fun w : Vector3 ℕ 4 => dpProdN (w &2) (w &3))
      = (fun w : Vector3 ℕ 4 => w &3 * (1 + w &2 * w &3) ^ w &2 + 1) := by
    funext w
    rfl
  exact hfun ▸ hN

/-- The product witness expression as a Diophantine function. -/
private theorem dp_prodRHS_diophFn :
    Dioph.DiophFn (fun w : Vector3 ℕ 4 =>
      ((w &3) ^ (w &2) * ((w &2)! * ((w &0 + w &2).choose (w &2))))
        % dpProdN (w &2) (w &3)) := by
  have hx : Dioph.DiophFn (fun w : Vector3 ℕ 4 => w &2) :=
    Dioph.proj_dioph_of_nat 2
  have ht : Dioph.DiophFn (fun w : Vector3 ℕ 4 => w &3) :=
    Dioph.proj_dioph_of_nat 3
  have hq : Dioph.DiophFn (fun w : Vector3 ℕ 4 => w &0) :=
    Dioph.proj_dioph_of_nat 0
  have hpw : Dioph.DiophFn (fun w : Vector3 ℕ 4 => (w &3) ^ (w &2)) :=
    Dioph.pow_dioph ht hx
  have hfact : Dioph.DiophFn (fun w : Vector3 ℕ 4 => (w &2)!) :=
    Dioph.diophFn_comp dp_factorial_diophFn [(fun w : Vector3 ℕ 4 => w &2)] hx
  have hqx : Dioph.DiophFn (fun w : Vector3 ℕ 4 => w &0 + w &2) :=
    Dioph.add_dioph hq hx
  have hchoose : Dioph.DiophFn
      (fun w : Vector3 ℕ 4 => (w &0 + w &2).choose (w &2)) :=
    Dioph.diophFn_comp dp_choose_diophFn
      [(fun w : Vector3 ℕ 4 => w &0 + w &2), (fun w : Vector3 ℕ 4 => w &2)]
      ⟨hqx, hx⟩
  exact Dioph.mod_dioph (Dioph.mul_dioph hpw (Dioph.mul_dioph hfact hchoose))
    dp_prodN_diophFn

/-- The graph of the product `Π_{j<x} (1 + (j+1) * t)` is Diophantine. -/
private theorem dp_prod_dioph :
    Dioph {v : Vector3 ℕ 3 | 1 ≤ v &2 ∧ v &0 = dpProdP (v &1) (v &2)} := by
  have hz : Dioph.DiophFn (fun w : Vector3 ℕ 4 => w &1) :=
    Dioph.proj_dioph_of_nat 1
  have hq : Dioph.DiophFn (fun w : Vector3 ℕ 4 => w &0) :=
    Dioph.proj_dioph_of_nat 0
  have ht : Dioph.DiophFn (fun w : Vector3 ℕ 4 => w &3) :=
    Dioph.proj_dioph_of_nat 3
  have hc1 : Dioph.DiophFn (fun _ : Vector3 ℕ 4 => (1 : ℕ)) := Dioph.const_dioph 1
  have h1t : Dioph {w : Vector3 ℕ 4 | 1 ≤ w &3} :=
    Dioph.le_dioph (Dioph.const_dioph 1) ht
  have hmod : Dioph {w : Vector3 ℕ 4 |
      w &3 * w &0 ≡ 1 [MOD dpProdN (w &2) (w &3)]} :=
    Dioph.modEq_dioph (Dioph.mul_dioph ht hq) (Dioph.const_dioph 1)
      dp_prodN_diophFn
  have heq : Dioph {w : Vector3 ℕ 4 | w &1 =
      (((w &3) ^ (w &2) * ((w &2)! * ((w &0 + w &2).choose (w &2))))
        % dpProdN (w &2) (w &3))} :=
    Dioph.eq_dioph hz dp_prodRHS_diophFn
  have hS4 : Dioph {w : Vector3 ℕ 4 | 1 ≤ w &3 ∧
      w &3 * w &0 ≡ 1 [MOD dpProdN (w &2) (w &3)] ∧ w &1 =
      (((w &3) ^ (w &2) * ((w &2)! * ((w &0 + w &2).choose (w &2))))
        % dpProdN (w &2) (w &3))} :=
    Dioph.ext ((h1t.inter hmod).inter heq) fun w => by
      simp only [Set.mem_inter_iff]
      constructor
      · rintro ⟨⟨a, b⟩, c⟩
        exact ⟨a, b, c⟩
      · rintro ⟨a, b, c⟩
        exact ⟨⟨a, b⟩, c⟩
  have hex := Dioph.vec_ex1_dioph 3 hS4
  have e0 : ∀ (q : ℕ) (v : Vector3 ℕ 3), (q :: v) &0 = q := fun _ _ => rfl
  have e1 : ∀ (q : ℕ) (v : Vector3 ℕ 3), (q :: v) &1 = v &0 := fun _ _ => rfl
  have e2 : ∀ (q : ℕ) (v : Vector3 ℕ 3), (q :: v) &2 = v &1 := fun _ _ => rfl
  have e3 : ∀ (q : ℕ) (v : Vector3 ℕ 3), (q :: v) &3 = v &2 := fun _ _ => rfl
  refine Dioph.ext hex fun v => ?_
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨q, h1, h2, h3⟩
    rw [e3 q v] at h1
    rw [e3 q v, e0 q v, e2 q v] at h2
    rw [e1 q v, e3 q v, e2 q v, e0 q v] at h3
    refine ⟨h1, ?_⟩
    have hiff := (dp_prod_iff (v &1) (v &2) (v &0) h1).mpr
    exact hiff ⟨q, h2, h3⟩
  · rintro ⟨h1, hz⟩
    have hiff := (dp_prod_iff (v &1) (v &2) (v &0) h1).mp hz
    obtain ⟨q, h2, h3⟩ := hiff
    refine ⟨q, ?_, ?_, ?_⟩
    · rw [e3 q v]; exact h1
    · rw [e3 q v, e0 q v, e2 q v]; exact h2
    · rw [e1 q v, e3 q v, e2 q v, e0 q v]; exact h3

/-- Forward direction of the recursion characterization: values come from a sequence. -/
private theorem dp_prec_fwd (f g : ℕ →. ℕ) (a : ℕ) :
    ∀ (n y : ℕ),
      y ∈ Nat.rec (motive := fun _ => Part ℕ) (f a)
        (fun k (IH : Part ℕ) => do
          let i ← IH; g (Nat.pair a (Nat.pair k i))) n →
      ∃ s : ℕ → ℕ, s 0 ∈ f a ∧
        (∀ k, k < n → s (k + 1) ∈ g (Nat.pair a (Nat.pair k (s k)))) ∧ s n = y := by
  intro n
  induction n with
  | zero =>
    intro y hy
    exact ⟨fun _ => y, hy, fun k hk => absurd hk (Nat.not_lt_zero k), rfl⟩
  | succ n ih =>
    intro y hy
    have hyb : y ∈ (Nat.rec (motive := fun _ => Part ℕ) (f a)
        (fun k (IH : Part ℕ) => do
          let i ← IH; g (Nat.pair a (Nat.pair k i))) n).bind
        (fun i => g (Nat.pair a (Nat.pair n i))) := hy
    obtain ⟨i, hii, hgi⟩ := Part.mem_bind_iff.mp hyb
    obtain ⟨s, hs0, hsS, hsn⟩ := ih i hii
    refine ⟨fun k => if k = n + 1 then y else s k, ?_, ?_, ?_⟩
    · have e0 : (fun k => if k = n + 1 then y else s k) 0 = s 0 :=
        ite_eq_right (by omega)
      rw [e0]
      exact hs0
    · intro k hk
      by_cases hkk : k + 1 = n + 1
      · have hkn : k = n := by omega
        have e1 : (fun k => if k = n + 1 then y else s k) (k + 1) = y :=
          ite_eq_left hkk
        have e2 : (fun k => if k = n + 1 then y else s k) k = s k :=
          ite_eq_right (by omega)
        rw [e1, e2, hkn, hsn]
        exact hgi
      · have e1 : (fun k => if k = n + 1 then y else s k) (k + 1) = s (k + 1) :=
          ite_eq_right hkk
        have e2 : (fun k => if k = n + 1 then y else s k) k = s k :=
          ite_eq_right (by omega)
        rw [e1, e2]
        exact hsS k (by omega)
    · exact ite_eq_left rfl

/-- Backward direction: a β-coded sequence runs inside the recursion. -/
private theorem dp_prec_bwd (f g : ℕ →. ℕ) (a c : ℕ)
    (h0 : Nat.beta c 0 ∈ f a) :
    ∀ (k : ℕ),
      (∀ j, j < k →
        Nat.beta c (j + 1) ∈ g (Nat.pair a (Nat.pair j (Nat.beta c j)))) →
      Nat.beta c k ∈ Nat.rec (motive := fun _ => Part ℕ) (f a)
        (fun j (IH : Part ℕ) => do
          let i ← IH; g (Nat.pair a (Nat.pair j i))) k := by
  intro k
  induction k with
  | zero =>
    intro _
    exact h0
  | succ k ih =>
    intro hall
    exact Part.mem_bind_iff.mpr
      ⟨Nat.beta c k, ih (fun j hj => hall j (by omega)),
        hall k (Nat.lt_succ_self k)⟩

/-- Membership in a primitive recursion via β-codes. -/
private theorem dp_prec_iff (f g : ℕ →. ℕ) (a n y : ℕ) :
    y ∈ Nat.rec (motive := fun _ => Part ℕ) (f a)
      (fun k (IH : Part ℕ) => do
        let i ← IH; g (Nat.pair a (Nat.pair k i))) n ↔
      ∃ c, Nat.beta c 0 ∈ f a ∧
        (∀ k, k < n →
          Nat.beta c (k + 1) ∈ g (Nat.pair a (Nat.pair k (Nat.beta c k)))) ∧
        y = Nat.beta c n := by
  constructor
  · intro hy
    obtain ⟨s, hs0, hsS, hsn⟩ := dp_prec_fwd f g a n y hy
    obtain ⟨c, hc⟩ := dp_beta_exists (List.ofFn (fun k : Fin (n + 1) => s k))
    have hlen : (List.ofFn (fun k : Fin (n + 1) => s k)).length = n + 1 :=
      List.length_ofFn
    have digit : ∀ (i : ℕ)
        (h : i < (List.ofFn (fun k : Fin (n + 1) => s k)).length),
        (List.ofFn (fun k : Fin (n + 1) => s k))[i] = s i :=
      fun i h => List.getElem_ofFn h
    refine ⟨c, ?_, ?_, ?_⟩
    · have hb := hc 0 (by rw [hlen]; omega)
      rw [hb, digit 0 (by rw [hlen]; omega)]
      exact hs0
    · intro k hk
      have hb1 := hc (k + 1) (by rw [hlen]; omega)
      have hb0 : Nat.beta c k = s k := by
        rw [hc k (by rw [hlen]; omega), digit k (by rw [hlen]; omega)]
      rw [hb1, digit (k + 1) (by rw [hlen]; omega), hb0]
      exact hsS k hk
    · have hb := hc n (by rw [hlen]; omega)
      have e := digit n (by rw [hlen]; omega)
      rw [← hsn, ← e, ← hb]
  · rintro ⟨c, h0, hall, rfl⟩
    exact dp_prec_bwd f g a c h0 n hall

/-- Readings of polynomial variables in a list code are primitive recursive. -/
private theorem dp_read_primrec (m : ℕ) :
    ∀ i : Unit ⊕ Fin m,
      Primrec (fun s : ℕ × List ℕ => match i with
        | Sum.inl _ => s.1 | Sum.inr j => s.2.getD (j : ℕ) 0) := by
  intro i
  cases i with
  | inl _ => exact Primrec.fst
  | inr j =>
    have hget : Primrec₂ (fun l : List ℕ => fun n : ℕ => l.getD n 0) :=
      Primrec.list_getD 0
    have hsnd : Primrec (fun s : ℕ × List ℕ => s.2) := Primrec.snd
    have hcj : Primrec (fun _ : ℕ × List ℕ => (j : ℕ)) := Primrec.const (j : ℕ)
    exact Primrec₂.comp (f := fun l : List ℕ => fun n : ℕ => l.getD n 0)
      (g := fun s : ℕ × List ℕ => s.2) (h := fun _ : ℕ × List ℕ => (j : ℕ))
      hget hsnd hcj

/-- A Diophantine set of naturals, rephrased over list codes. -/
private theorem dp_list_key (S : Set ℕ) (m : ℕ) (p : Poly (Unit ⊕ Fin m))
    (hp : ∀ n, n ∈ S ↔ ∃ t : Fin m → ℕ, p (Sum.elim (fun _ => n) t) = 0)
    (F G : (Unit ⊕ Fin m → ℕ) → ℕ)
    (hpFG : ∀ v, p v = (F v : ℤ) - (G v : ℤ)) (n : ℕ) :
    n ∈ S ↔ ∃ l : List ℕ,
      F (fun (i : Unit ⊕ Fin m) => match i with
        | Sum.inl _ => (n, l).1 | Sum.inr j => (n, l).2.getD (j : ℕ) 0) =
      G (fun (i : Unit ⊕ Fin m) => match i with
        | Sum.inl _ => (n, l).1 | Sum.inr j => (n, l).2.getD (j : ℕ) 0) := by
  constructor
  · rintro hn
    obtain ⟨t, ht⟩ := (hp n).mp hn
    have hFG : F (Sum.elim (fun _ => n) t) = G (Sum.elim (fun _ => n) t) := by
      have h0 : (F (Sum.elim (fun _ => n) t) : ℤ) -
          (G (Sum.elim (fun _ => n) t) : ℤ) = 0 := by
        rw [← hpFG]
        exact ht
      omega
    refine ⟨List.ofFn t, ?_⟩
    have hval : (fun (i : Unit ⊕ Fin m) => match i with
        | Sum.inl _ => (n, List.ofFn t).1
        | Sum.inr j => (n, List.ofFn t).2.getD (j : ℕ) 0) =
        Sum.elim (fun _ => n) t := by
      funext i
      cases i with
      | inl _ => rfl
      | inr j =>
        change List.getD (List.ofFn t) (j : ℕ) 0 = t j
        have hlen : (List.ofFn t).length = m := List.length_ofFn
        have hn : (j : ℕ) < (List.ofFn t).length := by
          rw [hlen]
          exact j.isLt
        rw [List.getD_eq_getElem _ _ hn]
        exact List.getElem_ofFn hn
    rw [hval]
    exact hFG
  · rintro ⟨l, hl⟩
    have hFG : F (Sum.elim (fun _ => n) (fun (j : Fin m) => l.getD (j : ℕ) 0)) =
        G (Sum.elim (fun _ => n) (fun (j : Fin m) => l.getD (j : ℕ) 0)) := by
      have hval : (fun (i : Unit ⊕ Fin m) => match i with
          | Sum.inl _ => (n, l).1 | Sum.inr j => (n, l).2.getD (j : ℕ) 0) =
          Sum.elim (fun _ => n) (fun (j : Fin m) => l.getD (j : ℕ) 0) := by
        funext i
        cases i with
        | inl _ => rfl
        | inr _ => rfl
      rw [hval] at hl
      exact hl
    have hz : p (Sum.elim (fun _ => n) (fun (j : Fin m) => l.getD (j : ℕ) 0)) = 0 := by
      rw [hpFG]
      rw [hFG]
      exact sub_self _
    exact (hp n).mpr ⟨_, hz⟩

/-- The bound `Q(v, u)` for the bounded-quantifier argument. -/
private def dpBQ_Q {α : Type} (m : ℕ) (F G : (Option (Option α) ⊕ Fin m → ℕ) → ℕ)
    (v : Option α → ℕ) (u : ℕ) : ℕ :=
  F (Sum.elim (Option.elim' (v none) v) (fun _ => u)) +
    G (Sum.elim (Option.elim' (v none) v) (fun _ => u)) + v none + u + 1

/-- Values of `p` on bounded valuations are below `Q`. -/
private theorem dp_bq_bound {α : Type} (m : ℕ) (p : Poly (Option (Option α) ⊕ Fin m))
    (F G : (Option (Option α) ⊕ Fin m → ℕ) → ℕ)
    (hF : dpNatPoly F) (hG : dpNatPoly G)
    (hpFG : ∀ w, p w = (F w : ℤ) - (G w : ℤ))
    (v : Option α → ℕ) (u k : ℕ) (y : Fin m → ℕ)
    (hk : k ≤ v none) (hy : ∀ i, y i ≤ u) :
    (p (Sum.elim (Option.elim' k v) y)).natAbs < dpBQ_Q m F G v u := by
  have hle : ∀ i, Sum.elim (Option.elim' k v) y i ≤
      Sum.elim (Option.elim' (v none) v) (fun _ => u) i := by
    intro i
    cases i with
    | inl o =>
      cases o with
      | none => exact hk
      | some _ => exact le_rfl
    | inr j => exact hy j
  have hFle := dpNatPoly_mono hF hle
  have hGle := dpNatPoly_mono hG hle
  have habs := dp_isPoly_natAbs_le hpFG (Sum.elim (Option.elim' k v) y)
  unfold dpBQ_Q
  omega

/-- Distinct moduli `1 + (j+1) * t` are coprime. -/
private theorem dp_bq_coprime {α : Type} (m : ℕ)
    (F G : (Option (Option α) ⊕ Fin m → ℕ) → ℕ)
    (v : Option α → ℕ) (u j k : ℕ)
    (hjk : j < k) (hkx : k < v none)
    (t : ℕ) (ht : t = (dpBQ_Q m F G v u)!) :
    Nat.Coprime (1 + (j + 1) * t) (1 + (k + 1) * t) := by
  have hxQ : v none ≤ dpBQ_Q m F G v u := by
    unfold dpBQ_Q
    omega
  have hpos : 0 < (k + 1) - (j + 1) := by omega
  have hlt : (k + 1) - (j + 1) < v none := by
    calc (k + 1) - (j + 1) ≤ k := by omega
      _ < v none := hkx
  have hle : (k + 1) - (j + 1) ≤ dpBQ_Q m F G v u := le_trans (le_of_lt hlt) hxQ
  have hdiv : (k + 1) - (j + 1) ∣ t := by
    rw [ht]
    exact Nat.dvd_factorial hpos hle
  have h := Nat.coprime_mul_succ (n := j + 1) (m := k + 1) (a := t) hdiv
  rwa [show (1 : ℕ) + (j + 1) * t = (j + 1) * t + 1 from add_comm _ _,
    show (1 : ℕ) + (k + 1) * t = (k + 1) * t + 1 from add_comm _ _]

/-- A divisor of `1 + c * t` determines `c` mod `1 + (k+1) * t`. -/
private theorem dp_bq_cong (k c t : ℕ) (h : 1 + (k + 1) * t ∣ 1 + c * t) :
    c ≡ k + 1 [MOD 1 + (k + 1) * t] := by
  have e1 : 1 + c * t ≡ 0 [MOD 1 + (k + 1) * t] := Nat.modEq_zero_iff_dvd.mpr h
  have e2 : 1 + (k + 1) * t ≡ 0 [MOD 1 + (k + 1) * t] :=
    Nat.modEq_zero_iff_dvd.mpr dvd_rfl
  have e3 : 1 + c * t ≡ 1 + (k + 1) * t [MOD 1 + (k + 1) * t] := e1.trans e2.symm
  have e4 : c * t ≡ (k + 1) * t [MOD 1 + (k + 1) * t] := Nat.ModEq.add_left_cancel' 1 e3
  have hcop : Nat.Coprime (1 + (k + 1) * t) t :=
    (Nat.coprime_add_mul_right_left 1 t (k + 1)).mpr (Nat.coprime_one_left t)
  exact Nat.ModEq.cancel_right_of_coprime hcop e4

/-- Prime divisors of `1 + (k+1) * Q!` exceed `Q`. -/
private theorem dp_bq_prime_big {α : Type} (m : ℕ)
    (F G : (Option (Option α) ⊕ Fin m → ℕ) → ℕ)
    (v : Option α → ℕ) (u k : ℕ)
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ)
    (hdvd : ℓ ∣ 1 + (k + 1) * (dpBQ_Q m F G v u)!) :
    dpBQ_Q m F G v u < ℓ := by
  by_contra hcon
  have hle : ℓ ≤ dpBQ_Q m F G v u := not_lt.mp hcon
  have hfact : ℓ ∣ (dpBQ_Q m F G v u)! :=
    Nat.dvd_factorial hℓ.pos hle
  have hmul : ℓ ∣ (k + 1) * (dpBQ_Q m F G v u)! :=
    dvd_mul_of_dvd_right hfact _
  have hsub := Nat.dvd_sub hdvd hmul
  rw [Nat.add_sub_cancel] at hsub
  have h1 : ℓ = 1 := Nat.dvd_one.mp hsub
  have hlt := hℓ.one_lt
  omega

/-- The product `Π_{j<x} (1 + (j+1) * t)` has the form `1 + c * t`. -/
private theorem dp_bq_prod_form (x t : ℕ) :
    ∃ c, (∏ j ∈ Finset.range x, (1 + (j + 1) * t)) = 1 + c * t := by
  induction x with
  | zero => exact ⟨0, by simp⟩
  | succ x ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c + (x + 1) + c * (x + 1) * t, by rw [Finset.prod_range_succ, hc]; ring⟩

/-- A difference `n - j` divides the descending factorial. -/
private theorem dp_bq_descFactorial_dvd (n u : ℕ) :
    ∀ j, j ≤ u → (n - j) ∣ n.descFactorial (u + 1) := by
  intro j
  induction u with
  | zero =>
    intro hj
    have hj0 : j = 0 := Nat.le_zero.mp hj
    subst hj0
    simp [Nat.descFactorial_succ, Nat.descFactorial_zero, mul_one]
  | succ u ih =>
    intro hj
    rw [Nat.descFactorial_succ]
    by_cases hju : j = u + 1
    · subst hju
      exact ⟨_, rfl⟩
    · obtain ⟨c, hc⟩ := ih (by omega)
      exact ⟨(n - (u + 1)) * c, by rw [hc]; ring⟩

/-- Pairwise-coprime divisors collectively divide via their product. -/
private theorem dp_bq_prod_dvd (s : ℕ → ℕ) (D x : ℕ)
    (hdiv : ∀ k < x, s k ∣ D)
    (hcop : ∀ j < x, ∀ k < x, j ≠ k → Nat.Coprime (s j) (s k)) :
    (∏ j ∈ Finset.range x, s j) ∣ D := by
  induction x with
  | zero => simp
  | succ x ih =>
    rw [Finset.prod_range_succ]
    have h1 : (∏ j ∈ Finset.range x, s j) ∣ D :=
      ih (fun k hk => hdiv k (by omega)) (fun j hj k hk hjk => hcop j (by omega) k (by omega) hjk)
    have h2 : s x ∣ D := hdiv x (Nat.lt_succ_self x)
    have hcop' : Nat.Coprime (∏ j ∈ Finset.range x, s j) (s x) := by
      apply Nat.Coprime.symm
      apply Nat.Coprime.prod_right
      intro j hj
      have hjx : j < x := Finset.mem_range.mp hj
      exact hcop x (Nat.lt_succ_self x) j (by omega) (by omega)
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop' h1 h2

/-- A prime divisor of a descending factorial divides one of its factors. -/
private theorem dp_bq_factor_dvd {ℓ n : ℕ} (hℓ : Nat.Prime ℓ) :
    ∀ (u : ℕ), ℓ ∣ n.descFactorial (u + 1) → ∃ j, j ≤ u ∧ ℓ ∣ n - j := by
  intro u
  induction u with
  | zero =>
    intro hdiv
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, mul_one] at hdiv
    exact ⟨0, le_rfl, hdiv⟩
  | succ u ih =>
    intro hdiv
    simp only [Nat.descFactorial_succ] at hdiv
    rcases (Nat.Prime.dvd_mul hℓ).mp hdiv with h | h
    · exact ⟨u + 1, le_rfl, h⟩
    · obtain ⟨j, hj, hjd⟩ := ih h
      exact ⟨j, by omega, hjd⟩

/-- Natural congruences give integer congruences. -/
private theorem dp_bq_natModEq_int {a b n : ℕ} (h : a ≡ b [MOD n]) :
    (a : ℤ) ≡ (b : ℤ) [ZMOD (n : ℤ)] := by
  rw [Int.modEq_iff_dvd]
  rw [Nat.modEq_iff_dvd] at h
  exact h

/-- `Dioph` sets are closed under finite conjunctions over `Fin m`. -/
private theorem dp_dioph_fin_forall {V : Type} :
    ∀ (m : ℕ) (S : Fin m → Set (V → ℕ)),
      (∀ i, Dioph (S i)) → Dioph {w | ∀ i, w ∈ S i} := by
  intro m
  induction m with
  | zero =>
    intro S hS
    have huniv : Dioph (Set.univ : Set (V → ℕ)) := by
      refine Dioph.ext (Dioph.eq_dioph (Dioph.const_dioph 0)
        (Dioph.const_dioph 0)) fun w => ?_
      simp
    have hempty : {w : V → ℕ | ∀ i, w ∈ S i} = Set.univ :=
      Set.eq_univ_of_forall fun w i => Fin.elim0 i
    rw [hempty]
    exact huniv
  | succ m ih =>
    intro S hS
    have hsplit : {w : V → ℕ | ∀ i, w ∈ S i}
        = S 0 ∩ {w | ∀ j : Fin m, w ∈ S j.succ} := by
      ext w
      simp only [Set.mem_inter_iff]
      exact Fin.forall_fin_succ
    rw [hsplit]
    exact (hS 0).inter (ih _ (fun j => hS j.succ))

/-- Variable map for the `Q` bound in the bounded-quantifier matrix. -/
private def dpBQ_σQ {α : Type} (m : ℕ) :
    (Option (Option α) ⊕ Fin m) → ((Option α) ⊕ (Fin 3 ⊕ Fin m)) :=
  fun i => match i with
  | Sum.inl none => Sum.inl none
  | Sum.inl (some o) => Sum.inl o
  | Sum.inr _ => Sum.inr (Sum.inl 0)

/-- Variable map for the polynomial in the bounded-quantifier matrix. -/
private def dpBQ_σP {α : Type} (m : ℕ) :
    (Option (Option α) ⊕ Fin m) → ((Option α) ⊕ (Fin 3 ⊕ Fin m)) :=
  fun i => match i with
  | Sum.inl none => Sum.inr (Sum.inl 2)
  | Sum.inl (some o) => Sum.inl o
  | Sum.inr j => Sum.inr (Sum.inr j)

/-- Davis's bounded-quantifier equivalence. -/
private theorem dp_bq_iff {α : Type} (m : ℕ) (p : Poly (Option (Option α) ⊕ Fin m))
    (F G : (Option (Option α) ⊕ Fin m → ℕ) → ℕ)
    (hF : dpNatPoly F) (hG : dpNatPoly G)
    (hpFG : ∀ w, p w = (F w : ℤ) - (G w : ℤ))
    (v : Option α → ℕ) :
    (∀ k < v none, ∃ y : Fin m → ℕ, p (Sum.elim (Option.elim' k v) y) = 0)
    ↔ ∃ u c e : ℕ, ∃ a : Fin m → ℕ,
      (1 + c * (dpBQ_Q m F G v u)!
        = ∏ j ∈ Finset.range (v none), (1 + (j + 1) * (dpBQ_Q m F G v u)!))
      ∧ (v none = 0 ∨ e + 1 = c)
      ∧ (∀ i, (1 + c * (dpBQ_Q m F G v u)!) ∣ (a i).descFactorial (u + 1))
      ∧ (1 + c * (dpBQ_Q m F G v u)!) ∣ (p (Sum.elim (Option.elim' e v) a)).natAbs := by
  set x := v none with hx
  constructor
  · intro H
    have Hfin : ∀ k : Fin x, ∃ y : Fin m → ℕ,
        p (Sum.elim (Option.elim' (k : ℕ) v) y) = 0 := fun k => H _ k.isLt
    have yex : ∀ k : ℕ, ∃ y0 : Fin m → ℕ,
        k < x → p (Sum.elim (Option.elim' k v) y0) = 0 := by
      intro k
      by_cases hk : k < x
      · obtain ⟨y0, hy0⟩ := Hfin ⟨k, hk⟩
        exact ⟨y0, fun _ => hy0⟩
      · exact ⟨fun _ => 0, fun h => absurd h hk⟩
    choose yk hyk using yex
    have hub : ∃ u, ∀ (k : ℕ) (hk : k < x) (i : Fin m), yk k i ≤ u := by
      refine ⟨Finset.univ.sup (fun ki : Fin x × Fin m => yk ↑ki.1 ki.2), ?_⟩
      intro k hk i
      have hmem : ((⟨k, hk⟩ : Fin x), i) ∈
          (Finset.univ : Finset (Fin x × Fin m)) := Finset.mem_univ _
      have hle := Finset.le_sup (f := fun ki : Fin x × Fin m => yk ↑ki.1 ki.2) hmem
      simpa using hle
    obtain ⟨u, hub⟩ := hub
    set t := (dpBQ_Q m F G v u)! with ht
    have htpos : 0 < t := by rw [ht]; exact Nat.factorial_pos _
    have ht1 : 1 ≤ t := by omega
    obtain ⟨c, hc⟩ := dp_bq_prod_form x t
    have hcop_all : ∀ j < x, ∀ k < x, j ≠ k →
        Nat.Coprime (1 + (j + 1) * t) (1 + (k + 1) * t) := by
      intro j hj k hk hjk
      rcases lt_or_gt_of_ne hjk with h | h
      · exact dp_bq_coprime m F G v u j k h hk t ht
      · exact (dp_bq_coprime m F G v u k j h hj t ht).symm
    by_cases hx0 : x = 0
    · refine ⟨u, c, 0, fun _ => 0, hc.symm, Or.inl hx0, fun i => ?_, ?_⟩
      · have h1 : 1 + c * t = 1 := hc.symm.trans (by rw [hx0]; simp)
        rw [h1]
        exact one_dvd _
      · have h1 : 1 + c * t = 1 := hc.symm.trans (by rw [hx0]; simp)
        rw [h1]
        exact one_dvd _
    · have hx1 : 1 ≤ x := Nat.one_le_iff_ne_zero.mpr hx0
      have h0x : 0 < x := by omega
      have hc1 : 1 ≤ c := by
        have hmem : (0 : ℕ) ∈ Finset.range x := Finset.mem_range.mpr h0x
        have hdvd : (1 + (0 + 1) * t) ∣ ∏ j ∈ Finset.range x, (1 + (j + 1) * t) :=
          Finset.dvd_prod_of_mem _ hmem
        have hpos : 0 < ∏ j ∈ Finset.range x, (1 + (j + 1) * t) :=
          Finset.prod_pos (fun j _ => by omega)
        have hleP : 1 + (0 + 1) * t ≤ ∏ j ∈ Finset.range x, (1 + (j + 1) * t) :=
          Nat.le_of_dvd hpos hdvd
        by_contra hcon
        have hc0 : c = 0 := by omega
        rw [hc0, zero_mul, add_zero] at hc
        have e0 : (0 + 1) * t = t := by ring
        omega
      have he : c - 1 + 1 = c := Nat.sub_add_cancel hc1
      have crt : ∀ i : Fin m, ∃ ai, ∀ k < x, ai ≡ yk k i [MOD 1 + (k + 1) * t] := by
        intro i
        have hs : ∀ k ∈ Finset.range x, (1 + (k + 1) * t) ≠ 0 := by
          intro k _
          omega
        have pp : Set.Pairwise (Finset.range x)
            (Nat.Coprime on fun k => 1 + (k + 1) * t) := by
          intro j hj k hk hjk
          rw [Finset.mem_coe, Finset.mem_range] at hj hk
          rcases lt_or_gt_of_ne hjk with h | h
          · exact dp_bq_coprime m F G v u j k h hk t ht
          · exact (dp_bq_coprime m F G v u k j h hj t ht).symm
        obtain ⟨ai, hai⟩ :=
          Nat.chineseRemainderOfFinset (fun k => yk k i) (fun k => 1 + (k + 1) * t)
            (Finset.range x) hs pp
        refine ⟨ai, fun k hk => ?_⟩
        have h2 := hai k (Finset.mem_range.mpr hk)
        simpa using h2
      choose a ha using crt
      refine ⟨u, c, c - 1, a, hc.symm, Or.inr he, ?_, ?_⟩
      · intro i
        rw [hc.symm]
        apply dp_bq_prod_dvd _ _ x _ hcop_all
        intro k hk
        by_cases hai : a i < u + 1
        · rw [(Nat.descFactorial_eq_zero_iff_lt).mpr hai]
          exact dvd_zero _
        · have hai' : u + 1 ≤ a i := not_lt.mp hai
          have hle : yk k i ≤ a i :=
            le_trans (le_trans (hub k hk i) (Nat.le_succ u)) hai'
          have hmod : yk k i ≡ a i [MOD 1 + (k + 1) * t] := (ha i k hk).symm
          have hdvd : (1 + (k + 1) * t) ∣ a i - yk k i :=
            (Nat.modEq_iff_dvd' hle).mp hmod
          exact dvd_trans hdvd (dp_bq_descFactorial_dvd (a i) u (yk k i) (hub k hk i))
      · have hdivnat : ∀ k < x, (1 + (k + 1) * t) ∣
            (p (Sum.elim (Option.elim' (c - 1) v) a)).natAbs := by
          intro k hk
          have hM : (1 + (k + 1) * t) ∣ 1 + c * t := by
            rw [hc.symm]
            exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hk)
          have hcc : c ≡ k + 1 [MOD 1 + (k + 1) * t] := dp_bq_cong k c t hM
          have hek : (((c - 1 : ℕ) : ℤ)) ≡ ((k : ℕ) : ℤ)
              [ZMOD ((1 + (k + 1) * t : ℕ) : ℤ)] := by
            rw [Int.modEq_iff_dvd]
            rw [Nat.modEq_iff_dvd] at hcc
            have hcc' : (k : ℤ) - ((c - 1 : ℕ) : ℤ)
                = ((k + 1 : ℕ) : ℤ) - (c : ℤ) := by omega
            rwa [hcc']
          have hpoint : ∀ i : Option (Option α) ⊕ Fin m,
              (((Sum.elim (Option.elim' (c - 1) v) a) i : ℕ) : ℤ) ≡
              (((Sum.elim (Option.elim' k v) (yk k)) i : ℕ) : ℤ)
              [ZMOD ((1 + (k + 1) * t : ℕ) : ℤ)] := by
            intro i
            cases i with
            | inl o =>
              cases o with
              | none => exact hek
              | some _ => exact Int.ModEq.refl _
            | inr j => exact dp_bq_natModEq_int (ha j k hk)
          have hcong : p (Sum.elim (Option.elim' (c - 1) v) a) ≡
              p (Sum.elim (Option.elim' k v) (yk k))
              [ZMOD ((1 + (k + 1) * t : ℕ) : ℤ)] :=
            dp_isPoly_modEq p.isPoly hpoint
          have hy0 := hyk k hk
          rw [hy0, Int.modEq_zero_iff_dvd] at hcong
          exact (Int.natCast_dvd).mp hcong
        have hprod := dp_bq_prod_dvd _ _ x hdivnat hcop_all
        rwa [hc] at hprod
  · rintro ⟨u, c, e, a, hi, hii, hiii, hiv⟩
    intro k hk
    have hx1 : x ≠ 0 := by omega
    have hec : e + 1 = c := hii.resolve_left hx1
    set t := (dpBQ_Q m F G v u)! with ht
    have htpos : 0 < t := by rw [ht]; exact Nat.factorial_pos _
    have ht1 : 1 ≤ t := by omega
    have hMk : 1 + (k + 1) * t ≠ 1 := by
      have h1 : 0 < (k + 1) * t := Nat.mul_pos (by omega) htpos
      omega
    obtain ⟨ℓ, hℓprime, hℓdvd⟩ := Nat.exists_prime_and_dvd hMk
    have hMprod : (1 + (k + 1) * t) ∣ 1 + c * t := by
      rw [hi]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hk)
    have hℓct : ℓ ∣ 1 + c * t := dvd_trans hℓdvd hMprod
    have hcc : c ≡ k + 1 [MOD 1 + (k + 1) * t] := dp_bq_cong k c t hMprod
    have hccℓ : c ≡ k + 1 [MOD ℓ] := Nat.ModEq.of_dvd hℓdvd hcc
    have hekℓ : e ≡ k [MOD ℓ] := by
      rw [Nat.modEq_iff_dvd] at hccℓ ⊢
      have hcc' : (k : ℤ) - (e : ℤ) = ((k + 1 : ℕ) : ℤ) - (c : ℤ) := by omega
      rwa [hcc']
    have hQℓ : dpBQ_Q m F G v u < ℓ :=
      dp_bq_prime_big m F G v u k ℓ hℓprime hℓdvd
    have huQ : u < dpBQ_Q m F G v u := by unfold dpBQ_Q; omega
    have yex : ∀ i : Fin m, ∃ j, j ≤ u ∧ a i ≡ j [MOD ℓ] := by
      intro i
      by_cases hai : a i ≤ u
      · exact ⟨a i, hai, rfl⟩
      · have hai' : u < a i := not_le.mp hai
        have hℓd : ℓ ∣ (a i).descFactorial (u + 1) :=
          dvd_trans hℓct (hiii i)
        obtain ⟨j, hj, hjdvd⟩ := dp_bq_factor_dvd hℓprime u hℓd
        have hja : j ≤ a i := by omega
        have hmod : j ≡ a i [MOD ℓ] := (Nat.modEq_iff_dvd' hja).mpr hjdvd
        exact ⟨j, hj, hmod.symm⟩
    choose y hy using yex
    have hℓw0 : ((ℓ : ℕ) : ℤ) ∣ p (Sum.elim (Option.elim' e v) a) :=
      (Int.natCast_dvd).mpr (dvd_trans hℓct hiv)
    have hpoint : ∀ i : Option (Option α) ⊕ Fin m,
        (((Sum.elim (Option.elim' k v) y) i : ℕ) : ℤ) ≡
        (((Sum.elim (Option.elim' e v) a) i : ℕ) : ℤ) [ZMOD ((ℓ : ℕ) : ℤ)] := by
      intro i
      cases i with
      | inl o =>
        cases o with
        | none => exact (dp_bq_natModEq_int hekℓ).symm
        | some _ => exact Int.ModEq.refl _
      | inr j => exact dp_bq_natModEq_int ((hy j).2.symm)
    have hcong : p (Sum.elim (Option.elim' k v) y) ≡
        p (Sum.elim (Option.elim' e v) a) [ZMOD ((ℓ : ℕ) : ℤ)] :=
      dp_isPoly_modEq p.isPoly hpoint
    have hdvdint : ((ℓ : ℕ) : ℤ) ∣ p (Sum.elim (Option.elim' k v) y) := by
      have h0 : p (Sum.elim (Option.elim' e v) a) ≡ 0 [ZMOD ((ℓ : ℕ) : ℤ)] :=
        (Int.modEq_zero_iff_dvd).mpr hℓw0
      have hzz : p (Sum.elim (Option.elim' k v) y) ≡ 0 [ZMOD ((ℓ : ℕ) : ℤ)] :=
        hcong.trans h0
      exact (Int.modEq_zero_iff_dvd).mp hzz
    have hbound := dp_bq_bound m p F G hF hG hpFG v u k y hk.le (fun i => (hy i).1)
    have habs : |p (Sum.elim (Option.elim' k v) y)| < ((ℓ : ℕ) : ℤ) := by
      rw [← Int.natCast_natAbs]
      have h1 : (((p (Sum.elim (Option.elim' k v) y)).natAbs : ℕ) : ℤ) <
          ((dpBQ_Q m F G v u) : ℤ) := by exact_mod_cast hbound
      have h2 : ((dpBQ_Q m F G v u) : ℤ) < ((ℓ : ℕ) : ℤ) := by exact_mod_cast hQℓ
      omega
    have hzero := Int.eq_zero_of_abs_lt_dvd hdvdint habs
    exact ⟨y, hzero⟩

/-- The bounded universal quantifier preserves Diophantineness. -/
private theorem dp_bq_dioph {α : Type} (S : Set (Option (Option α) → ℕ))
    (hS : Dioph S) :
    Dioph {v : Option α → ℕ | ∀ k < v none, Option.elim' k v ∈ S} := by
  obtain ⟨m, p, hp0⟩ := dp_fin_dummies hS
  obtain ⟨F, G, hF, hG, hpFG⟩ := dp_isPoly_split p.isPoly
  have hp : ∀ w : Option (Option α) → ℕ,
      w ∈ S ↔ ∃ t : Fin m → ℕ, p (Sum.elim w t) = 0 := hp0
  have hrw : ∀ v : Option α → ℕ, (∀ k < v none, Option.elim' k v ∈ S) ↔
      (∃ u c e : ℕ, ∃ a : Fin m → ℕ,
        (1 + c * (dpBQ_Q m F G v u)!
          = ∏ j ∈ Finset.range (v none), (1 + (j + 1) * (dpBQ_Q m F G v u)!))
        ∧ (v none = 0 ∨ e + 1 = c)
        ∧ (∀ i, (1 + c * (dpBQ_Q m F G v u)!) ∣ (a i).descFactorial (u + 1))
        ∧ (1 + c * (dpBQ_Q m F G v u)!)
          ∣ (p (Sum.elim (Option.elim' e v) a)).natAbs) := by
    intro v
    simp only [hp]
    exact dp_bq_iff m p F G hF hG hpFG v
  refine Dioph.ext ?_ (fun v => (hrw v).symm)
  have hxW : Dioph.DiophFn
      (fun w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ => w (Sum.inl none)) :=
    Dioph.proj_dioph _
  have hcW : Dioph.DiophFn
      (fun w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ => w (Sum.inr (Sum.inl 1))) :=
    Dioph.proj_dioph _
  have huW : Dioph.DiophFn
      (fun w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ => w (Sum.inr (Sum.inl 0))) :=
    Dioph.proj_dioph _
  have heW : Dioph.DiophFn
      (fun w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ => w (Sum.inr (Sum.inl 2))) :=
    Dioph.proj_dioph _
  have hσQ : ∀ w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ, w ∘ dpBQ_σQ m =
      Sum.elim (Option.elim' (w (Sum.inl none)) (fun o => w (Sum.inl o)))
        (fun _ => w (Sum.inr (Sum.inl 0))) := by
    intro w
    funext i
    cases i with
    | inl o =>
      cases o with
      | none => rfl
      | some _ => rfl
    | inr _ => rfl
  have hσP : ∀ w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ, w ∘ dpBQ_σP m =
      Sum.elim (Option.elim' (w (Sum.inr (Sum.inl 2))) (fun o => w (Sum.inl o)))
        (fun j => w (Sum.inr (Sum.inr j))) := by
    intro w
    funext i
    cases i with
    | inl o =>
      cases o with
      | none => rfl
      | some _ => rfl
    | inr _ => rfl
  have hFQ' : Dioph.DiophFn (fun w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ =>
      F (Sum.elim (Option.elim' (w (Sum.inl none)) (fun o => w (Sum.inl o)))
        (fun _ => w (Sum.inr (Sum.inl 0))))) := by
    simpa only [hσQ] using Dioph.reindex_diophFn (dpBQ_σQ m)
      (dpNatPoly_diophFn hF)
  have hGQ' : Dioph.DiophFn (fun w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ =>
      G (Sum.elim (Option.elim' (w (Sum.inl none)) (fun o => w (Sum.inl o)))
        (fun _ => w (Sum.inr (Sum.inl 0))))) := by
    simpa only [hσQ] using Dioph.reindex_diophFn (dpBQ_σQ m)
      (dpNatPoly_diophFn hG)
  have hQ : Dioph.DiophFn (fun w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ =>
      dpBQ_Q m F G (fun o => w (Sum.inl o)) (w (Sum.inr (Sum.inl 0)))) :=
    Dioph.add_dioph (Dioph.add_dioph (Dioph.add_dioph (Dioph.add_dioph hFQ' hGQ')
      hxW) huW) (Dioph.const_dioph 1)
  have htW : Dioph.DiophFn (fun w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ =>
      (dpBQ_Q m F G (fun o => w (Sum.inl o)) (w (Sum.inr (Sum.inl 0))))!) :=
    Dioph.diophFn_comp dp_factorial_diophFn
      [fun w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ =>
        dpBQ_Q m F G (fun o => w (Sum.inl o)) (w (Sum.inr (Sum.inl 0)))] hQ
  have h1ct : Dioph.DiophFn (fun w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ =>
      1 + w (Sum.inr (Sum.inl 1)) *
        (dpBQ_Q m F G (fun o => w (Sum.inl o)) (w (Sum.inr (Sum.inl 0))))!) :=
    Dioph.add_dioph (Dioph.const_dioph 1) (Dioph.mul_dioph hcW htW)
  have hvec : VectorAllP Dioph.DiophFn
      [fun w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ =>
          1 + w (Sum.inr (Sum.inl 1)) *
            (dpBQ_Q m F G (fun o => w (Sum.inl o)) (w (Sum.inr (Sum.inl 0))))!,
        fun w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ => w (Sum.inl none),
        fun w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ =>
          (dpBQ_Q m F G (fun o => w (Sum.inl o)) (w (Sum.inr (Sum.inl 0))))!] := by
    simp only [vectorAllP_cons, vectorAllP_nil, and_true]
    exact ⟨h1ct, hxW, htW⟩
  have Si : Dioph {w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ |
      1 ≤ (dpBQ_Q m F G (fun o => w (Sum.inl o)) (w (Sum.inr (Sum.inl 0))))!
      ∧ 1 + w (Sum.inr (Sum.inl 1)) *
          (dpBQ_Q m F G (fun o => w (Sum.inl o)) (w (Sum.inr (Sum.inl 0))))!
        = dpProdP (w (Sum.inl none))
          ((dpBQ_Q m F G (fun o => w (Sum.inl o)) (w (Sum.inr (Sum.inl 0))))!)} := by
    refine Dioph.ext (Dioph.dioph_comp dp_prod_dioph
      [fun w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ =>
          1 + w (Sum.inr (Sum.inl 1)) *
            (dpBQ_Q m F G (fun o => w (Sum.inl o)) (w (Sum.inr (Sum.inl 0))))!,
        fun w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ => w (Sum.inl none),
        fun w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ =>
          (dpBQ_Q m F G (fun o => w (Sum.inl o)) (w (Sum.inr (Sum.inl 0))))!]
      hvec) fun w => Iff.rfl
  have hA : Dioph {w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ |
      w (Sum.inl none) = 0} := Dioph.eq_dioph hxW (Dioph.const_dioph 0)
  have hB : Dioph {w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ |
      w (Sum.inr (Sum.inl 2)) + 1 = w (Sum.inr (Sum.inl 1))} :=
    Dioph.eq_dioph (Dioph.add_dioph heW (Dioph.const_dioph 1)) hcW
  have Sii : Dioph {w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ |
      w (Sum.inl none) = 0
      ∨ w (Sum.inr (Sum.inl 2)) + 1 = w (Sum.inr (Sum.inl 1))} :=
    Dioph.ext (Dioph.union hA hB) fun w => Iff.rfl
  have Siii : Dioph {w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ | ∀ i : Fin m,
      (1 + w (Sum.inr (Sum.inl 1)) *
        (dpBQ_Q m F G (fun o => w (Sum.inl o)) (w (Sum.inr (Sum.inl 0))))!)
      ∣ ((w (Sum.inr (Sum.inr i))).descFactorial (w (Sum.inr (Sum.inl 0)) + 1))} := by
    apply dp_dioph_fin_forall
    intro i
    exact Dioph.dvd_dioph h1ct (Dioph.diophFn_comp dp_descFactorial_diophFn
      [fun w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ => w (Sum.inr (Sum.inr i)),
        fun w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ =>
          w (Sum.inr (Sum.inl 0)) + 1]
      ⟨Dioph.proj_dioph _, Dioph.add_dioph huW (Dioph.const_dioph 1)⟩)
  have hPQ' : Dioph.DiophFn (fun w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ =>
      (p (Sum.elim (Option.elim' (w (Sum.inr (Sum.inl 2))) (fun o => w (Sum.inl o)))
        (fun j => w (Sum.inr (Sum.inr j))))).natAbs) := by
    simpa only [hσP] using Dioph.reindex_diophFn (dpBQ_σP m)
      (Dioph.abs_poly_dioph p)
  have Siv : Dioph {w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ |
      (1 + w (Sum.inr (Sum.inl 1)) *
        (dpBQ_Q m F G (fun o => w (Sum.inl o)) (w (Sum.inr (Sum.inl 0))))!)
      ∣ (p (Sum.elim (Option.elim' (w (Sum.inr (Sum.inl 2))) (fun o => w (Sum.inl o)))
        (fun j => w (Sum.inr (Sum.inr j))))).natAbs} :=
    Dioph.dvd_dioph h1ct hPQ'
  have hmat : Dioph {w : (Option α) ⊕ (Fin 3 ⊕ Fin m) → ℕ |
      (1 ≤ (dpBQ_Q m F G (fun o => w (Sum.inl o)) (w (Sum.inr (Sum.inl 0))))!
        ∧ 1 + w (Sum.inr (Sum.inl 1)) *
            (dpBQ_Q m F G (fun o => w (Sum.inl o)) (w (Sum.inr (Sum.inl 0))))!
          = dpProdP (w (Sum.inl none))
            ((dpBQ_Q m F G (fun o => w (Sum.inl o)) (w (Sum.inr (Sum.inl 0))))!))
      ∧ (w (Sum.inl none) = 0
        ∨ w (Sum.inr (Sum.inl 2)) + 1 = w (Sum.inr (Sum.inl 1)))
      ∧ (∀ i : Fin m,
        (1 + w (Sum.inr (Sum.inl 1)) *
          (dpBQ_Q m F G (fun o => w (Sum.inl o)) (w (Sum.inr (Sum.inl 0))))!)
        ∣ ((w (Sum.inr (Sum.inr i))).descFactorial (w (Sum.inr (Sum.inl 0)) + 1)))
      ∧ (1 + w (Sum.inr (Sum.inl 1)) *
          (dpBQ_Q m F G (fun o => w (Sum.inl o)) (w (Sum.inr (Sum.inl 0))))!)
        ∣ (p (Sum.elim (Option.elim' (w (Sum.inr (Sum.inl 2))) (fun o => w (Sum.inl o)))
          (fun j => w (Sum.inr (Sum.inr j))))).natAbs} := by
    refine Dioph.ext (Si.inter (Sii.inter (Siii.inter Siv))) fun w => ?_
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  have hpeel := Dioph.ex_dioph hmat
  refine Dioph.ext hpeel fun v => ?_
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨⟨hxle, hxeq⟩, hxii, hxiii, hxiv⟩ := hx
    refine ⟨x (Sum.inl 0), x (Sum.inl 1), x (Sum.inl 2), x ∘ Sum.inr,
      ?_, ?_, ?_, ?_⟩
    · exact hxeq
    · exact hxii
    · exact hxiii
    · exact hxiv
  · rintro ⟨u, c, e, a, hi, hii, hiii, hiv⟩
    refine ⟨Sum.elim (Fin.cons u (Fin.cons c (fun _ => e))) a, ?_⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · have ht1 : 1 ≤ (dpBQ_Q m F G v u)! :=
        Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
      exact ht1
    · exact hi
    · exact hii
    · exact hiii
    · exact hiv

/-- Composition tool: Diophantine graphs pull back along Diophantine functions. -/
private theorem dp_graph_comp {β : Type} {f : ℕ →. ℕ}
    {h₁ h₂ : (β → ℕ) → ℕ} (hf : Dioph {v : Vector3 ℕ 2 | v &1 ∈ f (v &0)})
    (hh₁ : Dioph.DiophFn h₁) (hh₂ : Dioph.DiophFn h₂) :
    Dioph {w : β → ℕ | h₂ w ∈ f (h₁ w)} := by
  have hvec : VectorAllP Dioph.DiophFn [h₁, h₂] := by
    simp only [vectorAllP_cons, vectorAllP_nil, and_true]
    exact ⟨hh₁, hh₂⟩
  exact Dioph.dioph_comp hf [h₁, h₂] hvec

/-- Membership in a pairing computation. -/
private theorem dp_pair_mem {f g : ℕ →. ℕ} (x y : ℕ) :
    y ∈ (fun n => Nat.pair <$> f n <*> g n) x ↔
    ∃ a b, a ∈ f x ∧ b ∈ g x ∧ Nat.pair a b = y := by
  simp only [seq_eq_bind_map, Part.bind_eq_bind, Part.map_eq_map,
    Part.mem_bind_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨a, ⟨a1, ha1, rfl⟩, b, hb, hab⟩
    exact ⟨a1, b, ha1, hb, hab⟩
  · rintro ⟨a1, b, ha1, hb, hab⟩
    exact ⟨Nat.pair a1, ⟨a1, ha1, rfl⟩, b, hb, hab⟩

/-- Membership in a composition computation. -/
private theorem dp_comp_mem {f g : ℕ →. ℕ} (x y : ℕ) :
    y ∈ (fun n => g n >>= f) x ↔ ∃ z, z ∈ g x ∧ y ∈ f z :=
  Part.mem_bind_iff

/-- Graphs of pairings are Diophantine. -/
private theorem dp_graph_pair {f g : ℕ →. ℕ}
    (ihf : Dioph {v : Vector3 ℕ 2 | v &1 ∈ f (v &0)})
    (ihg : Dioph {v : Vector3 ℕ 2 | v &1 ∈ g (v &0)}) :
    Dioph {v : Vector3 ℕ 2 |
      v &1 ∈ (fun n => Nat.pair <$> f n <*> g n) (v &0)} := by
  have h1 : Dioph {w : Vector3 ℕ 4 | w &1 ∈ f (w &2)} :=
    dp_graph_comp ihf (Dioph.proj_dioph_of_nat 2) (Dioph.proj_dioph_of_nat 1)
  have h2 : Dioph {w : Vector3 ℕ 4 | w &0 ∈ g (w &2)} :=
    dp_graph_comp ihg (Dioph.proj_dioph_of_nat 2) (Dioph.proj_dioph_of_nat 0)
  have h3 : Dioph {w : Vector3 ℕ 4 | Nat.pair (w &1) (w &0) = w &3} :=
    Dioph.eq_dioph (Dioph.diophFn_comp dp_pair_diophFn
      [fun w : Vector3 ℕ 4 => w &1, fun w : Vector3 ℕ 4 => w &0]
      ⟨Dioph.proj_dioph_of_nat 1, Dioph.proj_dioph_of_nat 0⟩)
      (Dioph.proj_dioph_of_nat 3)
  have hmat : Dioph {w : Vector3 ℕ 4 |
      (w &1 ∈ f (w &2) ∧ w &0 ∈ g (w &2))
      ∧ Nat.pair (w &1) (w &0) = w &3} :=
    Dioph.ext ((h1.inter h2).inter h3) fun w => Iff.rfl
  have hpeel1 : Dioph {v3 : Vector3 ℕ 3 |
      ∃ b, (b :: v3) ∈ {w : Vector3 ℕ 4 |
        (w &1 ∈ f (w &2) ∧ w &0 ∈ g (w &2))
        ∧ Nat.pair (w &1) (w &0) = w &3}} :=
    Dioph.vec_ex1_dioph 3 hmat
  have hpeel2 : Dioph {v : Vector3 ℕ 2 |
      ∃ a, (a :: v) ∈ {v3 : Vector3 ℕ 3 |
        ∃ b, (b :: v3) ∈ {w : Vector3 ℕ 4 |
          (w &1 ∈ f (w &2) ∧ w &0 ∈ g (w &2))
          ∧ Nat.pair (w &1) (w &0) = w &3}}} :=
    Dioph.vec_ex1_dioph 2 hpeel1
  refine Dioph.ext hpeel2 fun v => ?_
  simp only [Set.mem_ofPred_eq, dp_pair_mem]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, hab⟩
    exact ⟨a, b, ha, hb, hab⟩
  · rintro ⟨a, hh⟩
    obtain ⟨b, ha, hb, hab⟩ := hh
    exact ⟨a, b, ⟨ha, hb⟩, hab⟩

/-- Membership in the zero function. -/
private theorem dp_zero_mem (x y : ℕ) :
    y ∈ (pure 0 : ℕ →. ℕ) x ↔ y = 0 :=
  Part.mem_some_iff

/-- Membership in the successor function. -/
private theorem dp_succ_mem (x y : ℕ) :
    y ∈ (Nat.succ : ℕ →. ℕ) x ↔ y = x + 1 := by
  simp only [PFun.coe_val, Part.mem_some_iff, Nat.succ_eq_add_one]

/-- Membership in the first unpairing projection. -/
private theorem dp_left_mem (x y : ℕ) :
    y ∈ (↑(fun n : ℕ => n.unpair.1) : ℕ →. ℕ) x ↔ y = (Nat.unpair x).1 := by
  simp only [PFun.coe_val, Part.mem_some_iff]

/-- Membership in the second unpairing projection. -/
private theorem dp_right_mem (x y : ℕ) :
    y ∈ (↑(fun n : ℕ => n.unpair.2) : ℕ →. ℕ) x ↔ y = (Nat.unpair x).2 := by
  simp only [PFun.coe_val, Part.mem_some_iff]

/-- Graphs of zero are Diophantine. -/
private theorem dp_graph_zero :
    Dioph {v : Vector3 ℕ 2 | v &1 ∈ (pure 0 : ℕ →. ℕ) (v &0)} := by
  have hset : Dioph {v : Vector3 ℕ 2 | v &1 = 0} :=
    Dioph.eq_dioph (Dioph.proj_dioph_of_nat 1) (Dioph.const_dioph 0)
  refine Dioph.ext hset fun v => ?_
  simp only [dp_zero_mem]

/-- Graphs of successor are Diophantine. -/
private theorem dp_graph_succ :
    Dioph {v : Vector3 ℕ 2 | v &1 ∈ (Nat.succ : ℕ →. ℕ) (v &0)} := by
  have hset : Dioph {v : Vector3 ℕ 2 | v &1 = v &0 + 1} :=
    Dioph.eq_dioph (Dioph.proj_dioph_of_nat 1)
      (Dioph.add_dioph (Dioph.proj_dioph_of_nat 0) (Dioph.const_dioph 1))
  refine Dioph.ext hset fun v => ?_
  simp only [dp_succ_mem]

/-- Graphs of the first unpairing projection are Diophantine. -/
private theorem dp_graph_left :
    Dioph {v : Vector3 ℕ 2 |
      v &1 ∈ (↑(fun n : ℕ => n.unpair.1) : ℕ →. ℕ) (v &0)} := by
  have hset : Dioph {v : Vector3 ℕ 2 | v &1 = (Nat.unpair (v &0)).1} :=
    Dioph.eq_dioph (Dioph.proj_dioph_of_nat 1)
      (Dioph.diophFn_comp dp_unpair_fst_diophFn [(fun v : Vector3 ℕ 2 => v &0)]
        (Dioph.proj_dioph_of_nat 0))
  refine Dioph.ext hset fun v => ?_
  simp only [dp_left_mem]

/-- Graphs of the second unpairing projection are Diophantine. -/
private theorem dp_graph_right :
    Dioph {v : Vector3 ℕ 2 |
      v &1 ∈ (↑(fun n : ℕ => n.unpair.2) : ℕ →. ℕ) (v &0)} := by
  have hset : Dioph {v : Vector3 ℕ 2 | v &1 = (Nat.unpair (v &0)).2} :=
    Dioph.eq_dioph (Dioph.proj_dioph_of_nat 1)
      (Dioph.diophFn_comp dp_unpair_snd_diophFn [(fun v : Vector3 ℕ 2 => v &0)]
        (Dioph.proj_dioph_of_nat 0))
  refine Dioph.ext hset fun v => ?_
  simp only [dp_right_mem]

/-- Graphs of compositions are Diophantine. -/
private theorem dp_graph_comp_case {f g : ℕ →. ℕ}
    (ihf : Dioph {v : Vector3 ℕ 2 | v &1 ∈ f (v &0)})
    (ihg : Dioph {v : Vector3 ℕ 2 | v &1 ∈ g (v &0)}) :
    Dioph {v : Vector3 ℕ 2 | v &1 ∈ (fun n => g n >>= f) (v &0)} := by
  have h1 : Dioph {w : Vector3 ℕ 3 | w &0 ∈ g (w &1)} :=
    dp_graph_comp ihg (Dioph.proj_dioph_of_nat 1) (Dioph.proj_dioph_of_nat 0)
  have h2 : Dioph {w : Vector3 ℕ 3 | w &2 ∈ f (w &0)} :=
    dp_graph_comp ihf (Dioph.proj_dioph_of_nat 0) (Dioph.proj_dioph_of_nat 2)
  have hmat : Dioph {w : Vector3 ℕ 3 | w &0 ∈ g (w &1) ∧ w &2 ∈ f (w &0)} :=
    Dioph.ext (h1.inter h2) fun w => Iff.rfl
  have hpeel : Dioph {v : Vector3 ℕ 2 |
      ∃ z, (z :: v) ∈ {w : Vector3 ℕ 3 | w &0 ∈ g (w &1) ∧ w &2 ∈ f (w &0)}} :=
    Dioph.vec_ex1_dioph 2 hmat
  refine Dioph.ext hpeel fun v => ?_
  simp only [Set.mem_ofPred_eq, dp_comp_mem]
  constructor
  · rintro ⟨z, hgz, hfz⟩
    exact ⟨z, hgz, hfz⟩
  · rintro ⟨z, hgz, hfz⟩
    exact ⟨z, hgz, hfz⟩

/-- Membership in a primitive recursion via β-codes, with the input unpacked. -/
private theorem dp_prec_mem {f g : ℕ →. ℕ} (x y : ℕ) :
    y ∈ Nat.unpaired (fun a n => Nat.rec (motive := fun _ => Part ℕ) (f a)
      (fun k (IH : Part ℕ) => do let i ← IH; g (Nat.pair a (Nat.pair k i))) n) x ↔
    ∃ a n c, ((x = Nat.pair a n ∧ Nat.beta c 0 ∈ f a) ∧
      (∀ k < n, Nat.beta c (k + 1) ∈
        g (Nat.pair a (Nat.pair k (Nat.beta c k))))) ∧
      y = Nat.beta c n := by
  constructor
  · intro h
    have h' : y ∈ Nat.rec (motive := fun _ => Part ℕ) (f (Nat.unpair x).1)
        (fun k (IH : Part ℕ) => do
          let i ← IH; g (Nat.pair (Nat.unpair x).1 (Nat.pair k i)))
        (Nat.unpair x).2 := h
    obtain ⟨c, h0, hS, hy⟩ := (dp_prec_iff f g _ _ y).mp h'
    exact ⟨_, _, c, ⟨⟨(Nat.pair_unpair x).symm, h0⟩, hS⟩, hy⟩
  · rintro ⟨a, n, c, ⟨⟨hpair, h0⟩, hS⟩, hy⟩
    subst hpair
    have hun : ∀ (F : ℕ → ℕ → Part ℕ) (a n : ℕ),
        Nat.unpaired F (Nat.pair a n) = F a n := fun F a n => by
      simp only [Nat.unpaired, Nat.unpair_pair]
    rw [hun]
    change y ∈ Nat.rec (motive := fun _ => Part ℕ) (f a)
      (fun k (IH : Part ℕ) => do
        let i ← IH; g (Nat.pair a (Nat.pair k i))) n
    exact (dp_prec_iff f g a n y).mpr ⟨c, h0, hS, hy⟩

/-- Graphs of primitive recursions are Diophantine. -/
private theorem dp_graph_prec {f g : ℕ →. ℕ}
    (ihf : Dioph {v : Vector3 ℕ 2 | v &1 ∈ f (v &0)})
    (ihg : Dioph {v : Vector3 ℕ 2 | v &1 ∈ g (v &0)}) :
    Dioph {v : Vector3 ℕ 2 | v &1 ∈ Nat.unpaired (fun a n =>
      Nat.rec (motive := fun _ => Part ℕ) (f a)
        (fun k (IH : Part ℕ) => do
          let i ← IH; g (Nat.pair a (Nat.pair k i))) n) (v &0)} := by
  have hP1 : Dioph {w : Vector3 ℕ 5 | w &3 = Nat.pair (w &2) (w &1)} :=
    Dioph.eq_dioph (Dioph.proj_dioph_of_nat 3)
      (Dioph.diophFn_comp dp_pair_diophFn
        [fun w : Vector3 ℕ 5 => w &2, fun w : Vector3 ℕ 5 => w &1]
        ⟨Dioph.proj_dioph_of_nat 2, Dioph.proj_dioph_of_nat 1⟩)
  have hc0 : Dioph.DiophFn (fun w : Vector3 ℕ 5 => w &0) :=
    Dioph.proj_dioph_of_nat 0
  have hz5 : Dioph.DiophFn (fun _ : Vector3 ℕ 5 => (0 : ℕ)) :=
    Dioph.const_dioph 0
  have hbeta0 : Dioph.DiophFn
      (fun w : Vector3 ℕ 5 => Nat.beta (w &0) 0) :=
    Dioph.diophFn_comp dp_beta_diophFn
      [fun w : Vector3 ℕ 5 => w &0, fun _ : Vector3 ℕ 5 => 0] ⟨hc0, hz5⟩
  have hP2 : Dioph {w : Vector3 ℕ 5 | Nat.beta (w &0) 0 ∈ f (w &2)} :=
    dp_graph_comp ihf (Dioph.proj_dioph_of_nat 2) hbeta0
  have hbetan : Dioph.DiophFn
      (fun w : Vector3 ℕ 5 => Nat.beta (w &0) (w &1)) :=
    Dioph.diophFn_comp dp_beta_diophFn
      [fun w : Vector3 ℕ 5 => w &0, fun w : Vector3 ℕ 5 => w &1]
      ⟨hc0, Dioph.proj_dioph_of_nat 1⟩
  have hP4 : Dioph {w : Vector3 ℕ 5 | w &4 = Nat.beta (w &0) (w &1)} :=
    Dioph.eq_dioph (Dioph.proj_dioph_of_nat 4) hbetan
  have e1 : Dioph.DiophFn
      (fun u : Option (Option Bool) → ℕ => u (some (some true))) :=
    Dioph.proj_dioph _
  have e2 : Dioph.DiophFn (fun u : Option (Option Bool) → ℕ => u none) :=
    Dioph.proj_dioph _
  have e3 : Dioph.DiophFn
      (fun u : Option (Option Bool) → ℕ => u (some (some false))) :=
    Dioph.proj_dioph _
  have eb0 : Dioph.DiophFn (fun u : Option (Option Bool) → ℕ =>
      Nat.beta (u (some (some false))) (u none)) :=
    Dioph.diophFn_comp2 e3 e2 dp_beta_diophFn
  have einner : Dioph.DiophFn (fun u : Option (Option Bool) → ℕ =>
      Nat.pair (u none) (Nat.beta (u (some (some false))) (u none))) :=
    Dioph.diophFn_comp2 e2 eb0 dp_pair_diophFn
  have hstep₁ : Dioph.DiophFn (fun u : Option (Option Bool) → ℕ =>
      Nat.pair (u (some (some true)))
        (Nat.pair (u none) (Nat.beta (u (some (some false))) (u none)))) :=
    Dioph.diophFn_comp2 e1 einner dp_pair_diophFn
  have en1 : Dioph.DiophFn (fun u : Option (Option Bool) → ℕ => u none + 1) :=
    Dioph.add_dioph e2 (Dioph.const_dioph 1)
  have hstep₂ : Dioph.DiophFn (fun u : Option (Option Bool) → ℕ =>
      Nat.beta (u (some (some false))) (u none + 1)) :=
    Dioph.diophFn_comp2 e3 en1 dp_beta_diophFn
  have hS : Dioph {u : Option (Option Bool) → ℕ |
      Nat.beta (u (some (some false))) (u none + 1) ∈ g
        (Nat.pair (u (some (some true)))
          (Nat.pair (u none) (Nat.beta (u (some (some false))) (u none))))} :=
    dp_graph_comp ihg hstep₁ hstep₂
  have hT := dp_bq_dioph _ hS
  let σ : Option Bool → Fin2 5 := fun o => match o with
    | none => &1
    | some true => &2
    | some false => &0
  have hP3 : Dioph {w : Vector3 ℕ 5 | ∀ k < w &1,
      Nat.beta (w &0) (k + 1) ∈
        g (Nat.pair (w &2) (Nat.pair k (Nat.beta (w &0) k)))} :=
    Dioph.ext (Dioph.reindex_dioph _ σ hT) fun w => Iff.rfl
  have hmat : Dioph {w : Vector3 ℕ 5 |
      ((w &3 = Nat.pair (w &2) (w &1) ∧ Nat.beta (w &0) 0 ∈ f (w &2)) ∧
        (∀ k < w &1, Nat.beta (w &0) (k + 1) ∈
          g (Nat.pair (w &2) (Nat.pair k (Nat.beta (w &0) k))))) ∧
      w &4 = Nat.beta (w &0) (w &1)} :=
    Dioph.ext (((hP1.inter hP2).inter hP3).inter hP4) fun w => Iff.rfl
  have hpeel1 : Dioph {v4 : Vector3 ℕ 4 |
      ∃ c, (c :: v4) ∈ {w : Vector3 ℕ 5 |
        ((w &3 = Nat.pair (w &2) (w &1) ∧ Nat.beta (w &0) 0 ∈ f (w &2)) ∧
          (∀ k < w &1, Nat.beta (w &0) (k + 1) ∈
            g (Nat.pair (w &2) (Nat.pair k (Nat.beta (w &0) k))))) ∧
        w &4 = Nat.beta (w &0) (w &1)}} :=
    Dioph.vec_ex1_dioph 4 hmat
  have hpeel2 : Dioph {v3 : Vector3 ℕ 3 |
      ∃ n, (n :: v3) ∈ {v4 : Vector3 ℕ 4 |
        ∃ c, (c :: v4) ∈ {w : Vector3 ℕ 5 |
          ((w &3 = Nat.pair (w &2) (w &1) ∧ Nat.beta (w &0) 0 ∈ f (w &2)) ∧
            (∀ k < w &1, Nat.beta (w &0) (k + 1) ∈
              g (Nat.pair (w &2) (Nat.pair k (Nat.beta (w &0) k))))) ∧
          w &4 = Nat.beta (w &0) (w &1)}}} :=
    Dioph.vec_ex1_dioph 3 hpeel1
  have hpeel3 : Dioph {v : Vector3 ℕ 2 |
      ∃ a, (a :: v) ∈ {v3 : Vector3 ℕ 3 |
        ∃ n, (n :: v3) ∈ {v4 : Vector3 ℕ 4 |
          ∃ c, (c :: v4) ∈ {w : Vector3 ℕ 5 |
            ((w &3 = Nat.pair (w &2) (w &1) ∧ Nat.beta (w &0) 0 ∈ f (w &2)) ∧
              (∀ k < w &1, Nat.beta (w &0) (k + 1) ∈
                g (Nat.pair (w &2) (Nat.pair k (Nat.beta (w &0) k))))) ∧
            w &4 = Nat.beta (w &0) (w &1)}}}} :=
    Dioph.vec_ex1_dioph 2 hpeel2
  refine Dioph.ext hpeel3 fun v => ?_
  simp only [Set.mem_ofPred_eq, dp_prec_mem]
  constructor
  · rintro ⟨a, n, c, ⟨⟨hpair, h0⟩, hS⟩, hy⟩
    exact ⟨a, n, c, ⟨⟨hpair, h0⟩, hS⟩, hy⟩
  · rintro ⟨a, n, c, ⟨⟨hpair, h0⟩, hS⟩, hy⟩
    exact ⟨a, n, c, ⟨⟨hpair, h0⟩, hS⟩, hy⟩

/-- Membership in a minimization: `0` is hit at `y` and nowhere positive below. -/
private theorem dp_rfind_mem {f : ℕ →. ℕ} (x y : ℕ) :
    y ∈ (fun a => Nat.rfind fun n =>
      (fun m => decide (m = 0)) <$> f (Nat.pair a n)) x ↔
    0 ∈ f (Nat.pair x y) ∧
      ∀ k < y, ∃ m', m' ∈ f (Nat.pair x k) ∧ m' ≠ 0 := by
  change y ∈ Nat.rfind (fun n =>
    (fun m : ℕ => decide (m = 0)) <$> f (Nat.pair x n)) ↔ _
  refine Nat.mem_rfind.trans ?_
  constructor
  · rintro ⟨ht, hf⟩
    refine ⟨?_, fun k hk => ?_⟩
    · simp only [Part.map_eq_map, Part.mem_map_iff] at ht
      obtain ⟨m, hm, hdec⟩ := ht
      have hm0 : m = 0 := of_decide_eq_true hdec
      rwa [hm0] at hm
    · have hfk := hf hk
      simp only [Part.map_eq_map, Part.mem_map_iff] at hfk
      obtain ⟨m, hm, hdec⟩ := hfk
      exact ⟨m, hm, of_decide_eq_false hdec⟩
  · rintro ⟨h0, hall⟩
    refine ⟨?_, fun {m} hm => ?_⟩
    · simp only [Part.map_eq_map, Part.mem_map_iff]
      exact ⟨0, h0, rfl⟩
    · simp only [Part.map_eq_map, Part.mem_map_iff]
      obtain ⟨m', hm', hne⟩ := hall m hm
      exact ⟨m', hm', by simp [hne]⟩

/-- Graphs of minimizations are Diophantine. -/
private theorem dp_graph_rfind {f : ℕ →. ℕ}
    (ihf : Dioph {v : Vector3 ℕ 2 | v &1 ∈ f (v &0)}) :
    Dioph {v : Vector3 ℕ 2 | v &1 ∈ (fun a => Nat.rfind fun n =>
      (fun m => decide (m = 0)) <$> f (Nat.pair a n)) (v &0)} := by
  have hpairA : Dioph.DiophFn
      (fun v : Vector3 ℕ 2 => Nat.pair (v &0) (v &1)) :=
    Dioph.diophFn_comp dp_pair_diophFn
      [fun v : Vector3 ℕ 2 => v &0, fun v : Vector3 ℕ 2 => v &1]
      ⟨Dioph.proj_dioph_of_nat 0, Dioph.proj_dioph_of_nat 1⟩
  have hA : Dioph {v : Vector3 ℕ 2 | 0 ∈ f (Nat.pair (v &0) (v &1))} :=
    dp_graph_comp ihf hpairA (Dioph.const_dioph 0)
  have hpairS : Dioph.DiophFn (fun w : Option (Option (Option Unit)) → ℕ =>
      Nat.pair (w (some (some (some ())))) (w (some none))) :=
    Dioph.diophFn_comp2 (Dioph.proj_dioph _) (Dioph.proj_dioph _)
      dp_pair_diophFn
  have hA' : Dioph {w : Option (Option (Option Unit)) → ℕ |
      w none ∈ f (Nat.pair (w (some (some (some ())))) (w (some none)))} :=
    dp_graph_comp ihf hpairS (Dioph.proj_dioph _)
  have hB' : Dioph {w : Option (Option (Option Unit)) → ℕ | w none ≠ 0} :=
    Dioph.ne_dioph (Dioph.proj_dioph _) (Dioph.const_dioph 0)
  have hSmat : Dioph {w : Option (Option (Option Unit)) → ℕ |
      (w none ∈ f (Nat.pair (w (some (some (some ())))) (w (some none)))) ∧
      w none ≠ 0} :=
    Dioph.ext (hA'.inter hB') fun w => Iff.rfl
  have hS : Dioph {u : Option (Option Unit) → ℕ |
      ∃ m', Option.elim' m' u ∈ {w : Option (Option (Option Unit)) → ℕ |
        (w none ∈ f (Nat.pair (w (some (some (some ())))) (w (some none)))) ∧
        w none ≠ 0}} :=
    Dioph.ext (Dioph.ex1_dioph hSmat) fun u => Iff.rfl
  have hT := dp_bq_dioph _ hS
  let σ : Option Unit → Fin2 2 := fun o => match o with
    | none => &1
    | some _ => &0
  have hB : Dioph {v : Vector3 ℕ 2 | ∀ k < v &1,
      ∃ m', m' ∈ f (Nat.pair (v &0) k) ∧ m' ≠ 0} :=
    Dioph.ext (Dioph.reindex_dioph _ σ hT) fun v => Iff.rfl
  refine Dioph.ext (hA.inter hB) fun v => ?_
  simp only [Set.mem_inter_iff, dp_rfind_mem]
  constructor
  · rintro ⟨hA', hB'⟩
    exact ⟨hA', hB'⟩
  · rintro ⟨hA', hB'⟩
    exact ⟨hA', hB'⟩

/-- Graphs of partial recursive functions are Diophantine. -/
private theorem dp_graph_dioph {f : ℕ →. ℕ} (hf : Nat.Partrec f) :
    Dioph {v : Vector3 ℕ 2 | v &1 ∈ f (v &0)} := by
  induction hf with
  | zero => exact dp_graph_zero
  | succ => exact dp_graph_succ
  | left => exact dp_graph_left
  | right => exact dp_graph_right
  | pair _ _ ihf ihg => exact dp_graph_pair ihf ihg
  | comp _ _ ihf ihg => exact dp_graph_comp_case ihf ihg
  | prec _ _ ihf ihg => exact dp_graph_prec ihf ihg
  | rfind _ ihf => exact dp_graph_rfind ihf

/-- Every recursively enumerable set of naturals is Diophantine. -/
private theorem dp_re_to_dioph {S : Set ℕ}
    (hS : REPred (fun n => n ∈ S)) :
    Dioph {v : Unit → ℕ | v () ∈ S} := by
  have hmap : Partrec (fun a : ℕ =>
      (Part.assert (a ∈ S) fun _ => Part.some ()).map (fun _ => (0 : ℕ))) :=
    hS.map (Computable.const (0 : ℕ)).to₂
  have hNat : Nat.Partrec (fun a : ℕ =>
      (Part.assert (a ∈ S) fun _ => Part.some ()).map (fun _ => (0 : ℕ))) :=
    Partrec.nat_iff.mp hmap
  have hdom : ∀ n, ((Part.assert (n ∈ S) fun _ => Part.some ()).map
      (fun _ => (0 : ℕ))).Dom ↔ n ∈ S := by
    intro n
    constructor
    · intro h
      obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp h
      rw [Part.mem_map_iff] at hy
      obtain ⟨u, hu, -⟩ := hy
      rw [Part.mem_assert_iff] at hu
      exact hu.1
    · intro h
      apply Part.dom_iff_mem.mpr
      refine ⟨0, ?_⟩
      rw [Part.mem_map_iff]
      exact ⟨(), Part.mem_assert_iff.mpr ⟨h, Part.mem_some_iff.mpr rfl⟩, rfl⟩
  have hgraph : Dioph {v : Vector3 ℕ 2 | v &1 ∈ (fun a : ℕ =>
      (Part.assert (a ∈ S) fun _ => Part.some ()).map
        (fun _ => (0 : ℕ))) (v &0)} :=
    dp_graph_dioph hNat
  have hswap : Dioph {w : Vector3 ℕ 2 | w &0 ∈ (fun a : ℕ =>
      (Part.assert (a ∈ S) fun _ => Part.some ()).map
        (fun _ => (0 : ℕ))) (w &1)} :=
    dp_graph_comp (f := fun a : ℕ =>
      (Part.assert (a ∈ S) fun _ => Part.some ()).map
        (fun _ => (0 : ℕ))) hgraph
      (Dioph.proj_dioph_of_nat 1) (Dioph.proj_dioph_of_nat 0)
  have hpeel : Dioph {w : Vector3 ℕ 1 | ∃ y, (y :: w) ∈
      {v : Vector3 ℕ 2 | v &0 ∈ (fun a : ℕ =>
        (Part.assert (a ∈ S) fun _ => Part.some ()).map
          (fun _ => (0 : ℕ))) (v &1)}} :=
    Dioph.vec_ex1_dioph 1 hswap
  let σ : Fin2 1 → Unit := fun _ => ()
  have hrei : Dioph {v : Unit → ℕ | ∃ y, (y :: v ∘ σ) ∈
      {v : Vector3 ℕ 2 | v &0 ∈ (fun a : ℕ =>
        (Part.assert (a ∈ S) fun _ => Part.some ()).map
          (fun _ => (0 : ℕ))) (v &1)}} :=
    Dioph.ext (Dioph.reindex_dioph _ σ hpeel) fun v => Iff.rfl
  refine Dioph.ext hrei fun v => ?_
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, hy⟩
    exact (hdom _).mp (Part.dom_iff_mem.mpr ⟨y, hy⟩)
  · intro h
    refine ⟨0, ?_⟩
    have h0 : (0 : ℕ) ∈ (Part.assert (v () ∈ S) fun _ => Part.some ()).map
        (fun _ => (0 : ℕ)) := by
      rw [Part.mem_map_iff]
      exact ⟨(), Part.mem_assert_iff.mpr
        ⟨h, Part.mem_some_iff.mpr rfl⟩, rfl⟩
    exact h0

/-- Every Diophantine set of naturals is recursively enumerable. -/
private theorem dp_dioph_to_re {S : Set ℕ}
    (hS : Dioph {v : Unit → ℕ | v () ∈ S}) :
    REPred (fun n => n ∈ S) := by
  obtain ⟨m, p, hp0⟩ := dp_fin_dummies hS
  obtain ⟨F, G, hF, hG, hpFG⟩ := dp_isPoly_split p.isPoly
  have hp : ∀ n : ℕ, n ∈ S ↔
      ∃ t : Fin m → ℕ, p (Sum.elim (fun _ => n) t) = 0 := by
    intro n
    have h := hp0 (fun _ => n)
    simp only [Set.mem_ofPred_eq] at h
    exact h
  have hFhat := dpNatPoly_primrec (dp_read_primrec m) hF
  have hGhat := dpNatPoly_primrec (dp_read_primrec m) hG
  have hOfNat : Primrec (Denumerable.ofNat (List ℕ)) := Primrec.ofNat (List ℕ)
  have hpair : Primrec (fun a : ℕ × ℕ => (a.1, Denumerable.ofNat (List ℕ) a.2)) :=
    Primrec.pair Primrec.fst (hOfNat.comp Primrec.snd)
  have hF₂ := hFhat.comp hpair
  have hG₂ := hGhat.comp hpair
  have hPred := PrimrecRel.comp Primrec.eq hF₂ hG₂
  have hDec := hPred.decide
  have hDec2 := Primrec₂.curry.mpr hDec
  have hComp2 := hDec2.to_comp
  have hPart₂ := hComp2.partrec₂
  have hRfind := Partrec.rfind hPart₂
  have hRE := hRfind.dom_re
  have hlist := dp_list_key S m p hp F G hpFG
  refine REPred.of_eq hRE fun n => ?_
  rw [Nat.rfind_dom]
  constructor
  · rintro ⟨w, hwT, -⟩
    rw [PFun.coe_val, Part.mem_some_iff] at hwT
    have hEq : F (fun i : Unit ⊕ Fin m => match i with
          | Sum.inl _ => n
          | Sum.inr j => (Denumerable.ofNat (List ℕ) w).getD (j : ℕ) 0) =
        G (fun i : Unit ⊕ Fin m => match i with
          | Sum.inl _ => n
          | Sum.inr j => (Denumerable.ofNat (List ℕ) w).getD (j : ℕ) 0) := by
      simpa using hwT.symm
    exact (hlist n).mpr ⟨Denumerable.ofNat (List ℕ) w, by exact hEq⟩
  · intro hn
    obtain ⟨l, hl⟩ := (hlist n).mp hn
    refine ⟨Encodable.encode l, ?_, ?_⟩
    · rw [PFun.coe_val, Part.mem_some_iff]
      have hEq : F (fun i : Unit ⊕ Fin m => match i with
            | Sum.inl _ => n
            | Sum.inr j =>
              (Denumerable.ofNat (List ℕ) (Encodable.encode l)).getD (j : ℕ) 0) =
          G (fun i : Unit ⊕ Fin m => match i with
            | Sum.inl _ => n
            | Sum.inr j =>
              (Denumerable.ofNat (List ℕ) (Encodable.encode l)).getD (j : ℕ) 0) := by
        rw [Denumerable.ofNat_encode]
        exact hl
      simpa using hEq
    · intro _ _
      rw [PFun.coe_val]
      exact Part.dom_iff_mem.mpr ⟨_, Part.mem_some_iff.mpr rfl⟩

end MathlibExt.NumberTheory.DPRMWanted

@[expose] public section

namespace MathlibExt.NumberTheory.DPRMWanted

/-!
# Davis–Putnam–Robinson–Matiyasevich theorem
This file proves the DPRM theorem.
-/

/--
**Davis–Putnam–Robinson–Matiyasevich theorem.** A set $S$ of natural numbers is recursively
enumerable if and only if it is Diophantine, that is, there is a polynomial $p$ with integer
coefficients such that $n \in S$ exactly when $p(n, t_1, \dots, t_k) = 0$ for some natural numbers
$t_1, \dots, t_k$.

Proves `Wanted` entry `dprm_theorem`.

Source: M. Davis, H. Putnam, J. Robinson, The decision problem for
exponential Diophantine equations, Ann. of Math. 74 (1961); Y. Matiyasevich, Enumerable sets are
Diophantine, Dokl. Akad. Nauk SSSR 191 (1970) 279–282; textbook in Matiyasevich, Hilbert's Tenth
Problem
-/
public theorem dprm_theorem
    (S : Set ℕ) : REPred (fun n => n ∈ S) ↔ Dioph {v : Unit → ℕ | v () ∈ S} :=
  ⟨dp_re_to_dioph, dp_dioph_to_re⟩

end MathlibExt.NumberTheory.DPRMWanted
