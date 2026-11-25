/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ConditionalMutualInformation
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
import MathlibExt.InformationTheory.GallagerExponent
import MathlibExt.InformationTheory.LogSum
import MathlibExt.InformationTheory.MutualInformationDPI
import MathlibExt.Probability.ProbabilityMassFunction.Uniform
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Shannon's channel coding theorem for discrete memoryless channels: weak converse

A discrete memoryless channel with finite input alphabet `α` and finite output alphabet `β` is a
stochastic matrix `W : α → PMF β`, used `n` times independently. Its capacity, in bits, is
`C(W) = sup_p I(X; Y)` over input laws `p`, where `(X, Y)` has law `p(a) W(a)(b)`; below it is
written inline as `⨆ p : PMF α, finiteMutualInformation (p.bind fun a => (W a).map (Prod.mk a))`.
The input alphabet is assumed nonempty (otherwise no codeword exists). A deterministic code of
blocklength `n` with `M` messages is an encoder `f : Fin M → (Fin n → α)` and a decoder
`g : (Fin n → β) → Fin M` without an erasure output; message `m` is decoded wrongly with probability
`W^{⊗n}(· | f m){y | g y ≠ m}`, the product law `Measure.pi fun i => (W (f m i)).toMeasure`.

The coding theorem as Polyanskiy and Wu state it has three parts: every rate below capacity is
achievable with vanishing maximal error, every rate above capacity forces the average error to one
(strong converse), and Fano's inequality bounds every code at every blocklength (weak converse).
Achievability is proved, by Gallager's random coding bound, as
`MathlibExt.InformationTheory.ChannelCodingAchievability.channelCoding_achievability`. The strong
converse is proved in `MathlibExt.InformationTheory.ChannelCodingStrongConverse`. The book's codes
may be randomised and their decoders may output an erasure. Both converse statements specialize to
deterministic erasure-free codes.

The weak converse is proved here as `channelCoding_weak_converse`.

## References

* Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University
  Press, 2025: Definition 19.2 (codes), Theorem 19.9 (Shannon), Corollary 19.5 (maximal error),
  Theorem 17.3 and Theorem 19.7 (weak converse), Theorem 22.1 (strong converse).
* C. E. Shannon, A mathematical theory of communication, Bell Syst. Tech. J. 27 (1948).
* J. Wolfowitz, The coding of messages subject to chance errors, Illinois J. Math. 1 (1957).
-/

namespace MathlibExt.InformationTheory.ChannelCodingWanted

open MeasureTheory _root_.InformationTheory

/-- Mutual information of a finite joint law, written as a Kullback–Leibler sum in nats,
divided by `log 2`. -/
private theorem mutualInfo_sum {α β : Type*} [Fintype α] [Fintype β] (p : PMF (α × β)) :
    finiteMutualInformation p =
      (∑ t, (p t).toReal * Real.log ((p t).toReal /
        (((p.map Prod.fst) t.1).toReal * ((p.map Prod.snd) t.2).toReal))) / Real.log 2 := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  have hα : MeasurableSingletonClass α := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  have hβ : MeasurableSingletonClass β := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  have hkl := toReal_klDiv_prod p
  have hsum := toReal_klDiv_eq_sum (μ := p.toMeasure)
    (ν := (p.map Prod.fst).toMeasure.prod (p.map Prod.snd).toMeasure)
    (toMeasure_absolutelyContinuous_prod p) (by simp)
  rw [finiteMutualInformation_eq]
  have hsing : ∀ t : α × β,
      ((p.map Prod.fst).toMeasure.prod (p.map Prod.snd).toMeasure).real {t} =
        ((p.map Prod.fst) t.1).toReal * ((p.map Prod.snd) t.2).toReal := by
    intro t
    rw [measureReal_def, ← Set.singleton_prod_singleton, Measure.prod_prod,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), ENNReal.toReal_mul]
  rw [hsum] at hkl
  simp only [toMeasure_real_singleton, hsing] at hkl
  rw [Fintype.sum_prod_type] at hkl
  rw [Fintype.sum_prod_type, eq_div_iff (Real.log_pos one_lt_two).ne']
  exact hkl.symm

/-- Two joint laws with the same atom probabilities have the same mutual information. -/
private theorem finiteMutualInformation_eq_of_toReal {α β : Type*} [Finite α] [Finite β]
    {p q : PMF (α × β)} (h : ∀ t, (p t).toReal = (q t).toReal) :
    finiteMutualInformation p = finiteMutualInformation q := by
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  rw [mutualInfo_sum, mutualInfo_sum]
  have hm1 : ∀ a, ((p.map Prod.fst) a).toReal = ((q.map Prod.fst) a).toReal := by
    intro a; rw [PMF.toReal_map_fst_apply, PMF.toReal_map_fst_apply]
    exact Finset.sum_congr rfl fun b _ => h (a, b)
  have hm2 : ∀ b, ((p.map Prod.snd) b).toReal = ((q.map Prod.snd) b).toReal := by
    intro b; rw [PMF.toReal_map_snd_apply, PMF.toReal_map_snd_apply]
    exact Finset.sum_congr rfl fun a _ => h (a, b)
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [h t, hm1 t.1, hm2 t.2]

/-- Mutual information is invariant under relabelling both coordinates by equivalences. -/
private theorem finiteMutualInformation_map_equiv {α β α' β' : Type*} [Finite α] [Finite β]
    [Finite α'] [Finite β'] (p : PMF (α × β)) (e : α ≃ α') (f : β ≃ β') :
    finiteMutualInformation (p.map (Prod.map e f)) = finiteMutualInformation p := by
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  let := Fintype.ofFinite α'
  let := Fintype.ofFinite β'
  have hf1 : Prod.fst ∘ Prod.map e f = e ∘ Prod.fst := funext fun _ => rfl
  have hf2 : Prod.snd ∘ Prod.map e f = f ∘ Prod.snd := funext fun _ => rfl
  have h1 : (p.map (Prod.map e f)).map Prod.fst = (p.map Prod.fst).map e := by
    rw [PMF.map_comp, hf1, ← PMF.map_comp]
  have h2 : (p.map (Prod.map e f)).map Prod.snd = (p.map Prod.snd).map f := by
    rw [PMF.map_comp, hf2, ← PMF.map_comp]
  have h3 : shannonEntropy (p.map (Prod.map e f)) = shannonEntropy p := by
    have hfun : (Prod.map e f : α × β → α' × β') = (e.prodCongr f : α × β → α' × β') :=
      funext fun _ => rfl
    rw [hfun]
    exact shannonEntropy_map_equiv _ _
  rw [finiteMutualInformation_eq, finiteMutualInformation_eq, h1, h2, h3,
    shannonEntropy_map_equiv _ e, shannonEntropy_map_equiv _ f]

/-- Mutual information is symmetric in the two coordinates. -/
private theorem finiteMutualInformation_map_swap {α β : Type*} [Finite α] [Finite β]
    (p : PMF (α × β)) :
    finiteMutualInformation (p.map Prod.swap) = finiteMutualInformation p := by
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  rw [finiteMutualInformation_eq, finiteMutualInformation_eq]
  have hf1 : Prod.fst ∘ (Prod.swap : α × β → β × α) = (Prod.snd : α × β → β) :=
    funext fun _ => rfl
  have hf2 : Prod.snd ∘ (Prod.swap : α × β → β × α) = (Prod.fst : α × β → α) :=
    funext fun _ => rfl
  have h1 : (p.map Prod.swap).map Prod.fst = p.map Prod.snd := by
    rw [PMF.map_comp, hf1]
  have h2 : (p.map Prod.swap).map Prod.snd = p.map Prod.fst := by
    rw [PMF.map_comp, hf2]
  have h3 : shannonEntropy (p.map Prod.swap) = shannonEntropy p := by
    have hfun : (Prod.swap : α × β → β × α) = (Equiv.prodComm α β : α × β → β × α) :=
      funext fun _ => rfl
    rw [hfun]
    exact shannonEntropy_map_equiv _ _
  rw [h1, h2, h3, add_comm]

/-- Data-processing inequality for a deterministic map of the second coordinate. -/
private theorem finiteMutualInformation_map_snd_le {α β γ : Type*} [Finite α] [Finite β]
    [Finite γ] (p : PMF (α × β)) (g : β → γ) :
    finiteMutualInformation (p.map (Prod.map id g)) ≤ finiteMutualInformation p := by
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  let := Fintype.ofFinite γ
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  let : MeasurableSpace γ := ⊤
  have hdα : DiscreteMeasurableSpace α := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hdβ : DiscreteMeasurableSpace β := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hdγ : DiscreteMeasurableSpace γ := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hmeas : Measurable (Prod.map (id : α → α) g) := Measurable.of_discrete
  have hg : Measurable g := Measurable.of_discrete
  have hsingα : MeasurableSingletonClass α := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hsingβ : MeasurableSingletonClass β := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hmap : ((p.map (Prod.map (id : α → α) g)).toMeasure : Measure (α × γ)) =
      p.toMeasure.map (Prod.map (id : α → α) g) :=
    (PMF.toMeasure_map _ _ hmeas).symm
  have hmu : (⟨(p.map (Prod.map (id : α → α) g)).toMeasure, inferInstance⟩ :
      ProbabilityMeasure (α × γ)) =
      ProbabilityMeasure.map (⟨p.toMeasure, inferInstance⟩ : ProbabilityMeasure (α × β))
        (Prod.map (id : α → α) g) := by
    apply ProbabilityMeasure.toMeasure_injective
    change (p.map (Prod.map (id : α → α) g)).toMeasure =
      p.toMeasure.map (Prod.map (id : α → α) g)
    exact hmap
  have hne : measureMutualInformation
      (⟨p.toMeasure, inferInstance⟩ : ProbabilityMeasure (α × β)) ≠ ⊤ := by
    rw [measureMutualInformation_toMeasure]
    exact ENNReal.ofReal_ne_top
  unfold finiteMutualInformation
  rw [hmu]
  exact ENNReal.toReal_mono hne (measureMutualInformation_map_le
    (⟨p.toMeasure, inferInstance⟩ : ProbabilityMeasure (α × β)) hg)

/-- Data-processing inequality for a deterministic map of the first coordinate, via swapping. -/
private theorem finiteMutualInformation_map_fst_le {α β α' : Type*} [Finite α] [Finite β]
    [Finite α'] (p : PMF (α × β)) (e : α → α') :
    finiteMutualInformation (p.map (Prod.map e id)) ≤ finiteMutualInformation p := by
  have hswap : (p.map (Prod.map e id)).map Prod.swap =
      (p.map Prod.swap).map (Prod.map id e) := by
    rw [PMF.map_comp, PMF.map_comp]
    exact congrArg (PMF.map · p) (funext fun t => rfl)
  rw [← finiteMutualInformation_map_swap (p.map (Prod.map e id)), hswap]
  exact (finiteMutualInformation_map_snd_le _ _).trans
    (le_of_eq (finiteMutualInformation_map_swap p))

/-- The atom of a law pushed forward by an equivalence, at the image of a point. -/
private theorem map_equiv_apply {δ ε : Type*} [Finite δ] (p : PMF δ) (e : δ ≃ ε) (d : δ) :
    (p.map e) (e d) = p d := by
  classical
  let := Fintype.ofFinite δ
  rw [PMF.map_apply, tsum_eq_single d]
  · simp
  · intro t ht
    by_cases h : e d = e t
    · exact absurd (e.injective h) (Ne.symm ht)
    · simp [h]

/-- The real mass of the atom of a law pushed forward by an equivalence. -/
private theorem map_equiv_apply_toReal {δ ε : Type*} [Finite δ] (p : PMF δ) (e : δ ≃ ε)
    (d : δ) : ((p.map e) (e d)).toReal = (p d).toReal := by
  rw [map_equiv_apply]

/-- Two probability mass functions with the same real atom masses are equal. -/
private theorem pmf_eq_of_toReal_eq {δ : Type*} {p q : PMF δ}
    (h : ∀ x, (p x).toReal = (q x).toReal) : p = q := by
  apply PMF.ext
  intro x
  exact (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp (h x)

/-- A law on a one-point alphabet has zero entropy. -/
private theorem shannonEntropy_eq_zero_of_subsingleton {δ : Type*} [Fintype δ] [Subsingleton δ]
    [Nonempty δ] (q : PMF δ) : shannonEntropy q = 0 := by
  obtain ⟨a⟩ := ‹Nonempty δ›
  have hq : q = PMF.pure a := by
    apply PMF.ext
    intro b
    have hb : b = a := Subsingleton.elim b a
    rw [hb]
    have h : q a = 1 := by
      have hts := q.tsum_coe
      rw [tsum_fintype, Fintype.sum_subsingleton _ a] at hts
      exact hts
    simp [PMF.pure_apply, h]
  rw [hq, shannonEntropy_pure]

/-- The atom of a joint law built from an input law and a channel. -/
private theorem bind_joint_apply_toReal {α β : Type*} [Finite α] [Finite β] (p : PMF α)
    (W : α → PMF β) (a : α) (b : β) :
    ((p.bind fun a' => (W a').map (Prod.mk a')) (a, b)).toReal =
      (p a).toReal * ((W a) b).toReal := by
  classical
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  have hbind : (p.bind fun a' => (W a').map (Prod.mk a')) (a, b) = p a * (W a) b := by
    rw [PMF.bind_apply]
    have hmap : ∀ a' : α, ((W a').map (Prod.mk a')) (a, b) =
        if a' = a then (W a) b else 0 := by
      intro a'
      rw [PMF.map_apply]
      rw [tsum_eq_single b]
      · by_cases ha : a' = a
        · subst ha; simp
        · simp [ha, Ne.symm ha]
      · intro c hc
        by_cases h : (a, b) = (a', c)
        · exact absurd (Prod.mk.inj h).2 (Ne.symm hc)
        · simp [h]
    rw [tsum_eq_single a]
    · simp [hmap]
    · intro a' ha
      simp [hmap, ha]
  rw [hbind, ENNReal.toReal_mul]

/-- The first marginal of a joint law built from an input law and a channel. -/
private theorem bind_fst_toReal {α β : Type*} [Finite α] [Finite β] (p : PMF α)
    (W : α → PMF β) (a : α) :
    (((p.bind fun a' => (W a').map (Prod.mk a')).map Prod.fst) a).toReal = (p a).toReal := by
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  rw [PMF.toReal_map_fst_apply]
  calc ∑ b, ((p.bind fun a' => (W a').map (Prod.mk a')) (a, b)).toReal
      = ∑ b, (p a).toReal * ((W a) b).toReal :=
        Finset.sum_congr rfl fun b _ => bind_joint_apply_toReal p W a b
    _ = (p a).toReal := by
        rw [← Finset.mul_sum,
          MathlibExt.InformationTheory.GallagerExponent.sum_toReal_eq_one, mul_one]

/-- The second marginal of a joint law built from an input law and a channel. -/
private theorem bind_snd_toReal {α β : Type*} [Fintype α] [Finite β] (p : PMF α)
    (W : α → PMF β) (b : β) :
    (((p.bind fun a' => (W a').map (Prod.mk a')).map Prod.snd) b).toReal =
      ∑ a, (p a).toReal * ((W a) b).toReal := by
  rw [PMF.toReal_map_snd_apply]
  exact Finset.sum_congr rfl fun a _ => bind_joint_apply_toReal p W a b

/-- The atom of a law pushed forward by a function, as a real number. -/
private theorem map_apply_toReal {δ α : Type*} [Fintype δ] [DecidableEq α] (r : PMF δ)
    (h : δ → α) (a : α) :
    ((r.map h) a).toReal = ∑ d, if h d = a then (r d).toReal else 0 := by
  classical
  have h1 : (r.map h) a = ∑ d, if h d = a then r d else 0 := by
    rw [PMF.map_apply, tsum_fintype]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hd : a = h d
    · rw [ite_eq_left hd, ite_eq_left hd.symm]
    · rw [ite_eq_right hd, ite_eq_right (fun hcon => hd hcon.symm)]
  rw [h1, ENNReal.toReal_sum (fun d _ => by split_ifs <;> simp [PMF.apply_ne_top])]
  exact Finset.sum_congr rfl fun d _ => by split_ifs <;> simp

section

variable {α₀ α₁ β₀ β₁ : Type*} [Fintype α₀] [Fintype α₁] [Fintype β₀] [Fintype β₁]

/-- The atom probabilities of a two-block joint law, as real numbers. -/
private noncomputable def joint2Atom (p : PMF (α₀ × α₁)) (W₀ : α₀ → PMF β₀)
    (W₁ : α₁ → PMF β₁) (t : (α₀ × α₁) × (β₀ × β₁)) : ℝ :=
  (p t.1).toReal * ((W₀ t.1.1) t.2.1).toReal * ((W₁ t.1.2) t.2.2).toReal

omit [Fintype α₀] [Fintype α₁] [Fintype β₀] [Fintype β₁] in
private theorem joint2Atom_nonneg (p : PMF (α₀ × α₁)) (W₀ : α₀ → PMF β₀)
    (W₁ : α₁ → PMF β₁) (t : (α₀ × α₁) × (β₀ × β₁)) : 0 ≤ joint2Atom p W₀ W₁ t := by
  unfold joint2Atom
  exact mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) ENNReal.toReal_nonneg

private theorem joint2Atom_sum (p : PMF (α₀ × α₁)) (W₀ : α₀ → PMF β₀)
    (W₁ : α₁ → PMF β₁) : ∑ t, joint2Atom p W₀ W₁ t = 1 := by
  classical
  rw [Fintype.sum_prod_type]
  have h0 : ∀ a : α₀, ∑ b : β₀, ((W₀ a) b).toReal = 1 :=
    fun a => MathlibExt.InformationTheory.GallagerExponent.sum_toReal_eq_one (W₀ a)
  have h1 : ∀ a : α₁, ∑ b : β₁, ((W₁ a) b).toReal = 1 :=
    fun a => MathlibExt.InformationTheory.GallagerExponent.sum_toReal_eq_one (W₁ a)
  calc ∑ x : α₀ × α₁, ∑ y : β₀ × β₁, joint2Atom p W₀ W₁ (x, y)
      = ∑ x : α₀ × α₁, (p x).toReal * (∑ y₀, ((W₀ x.1) y₀).toReal) *
          (∑ y₁, ((W₁ x.2) y₁).toReal) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Fintype.sum_prod_type]
        calc ∑ y₀ : β₀, ∑ y₁ : β₁, joint2Atom p W₀ W₁ (x, (y₀, y₁))
            = (p x).toReal * ((∑ y₀, ((W₀ x.1) y₀).toReal) *
                (∑ y₁, ((W₁ x.2) y₁).toReal)) := by
              rw [Fintype.sum_mul_sum]
              simp only [joint2Atom, Finset.mul_sum, mul_assoc]
          _ = (p x).toReal * (∑ y₀, ((W₀ x.1) y₀).toReal) *
              (∑ y₁, ((W₁ x.2) y₁).toReal) := by ring
    _ = ∑ x : α₀ × α₁, (p x).toReal := by
        simp [h0, h1]
    _ = 1 := MathlibExt.InformationTheory.GallagerExponent.sum_toReal_eq_one p

/-- The two-block joint law of an input law and two independent channels. -/
private noncomputable def joint2PMF (p : PMF (α₀ × α₁)) (W₀ : α₀ → PMF β₀)
    (W₁ : α₁ → PMF β₁) : PMF ((α₀ × α₁) × (β₀ × β₁)) :=
  PMF.ofFintype (fun t => ENNReal.ofReal (joint2Atom p W₀ W₁ t)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ => joint2Atom_nonneg p W₀ W₁ t),
      joint2Atom_sum, ENNReal.ofReal_one])

private theorem joint2PMF_apply_toReal (p : PMF (α₀ × α₁)) (W₀ : α₀ → PMF β₀)
    (W₁ : α₁ → PMF β₁) (t : (α₀ × α₁) × (β₀ × β₁)) :
    ((joint2PMF p W₀ W₁) t).toReal = joint2Atom p W₀ W₁ t :=
  ENNReal.toReal_ofReal (joint2Atom_nonneg p W₀ W₁ t)

omit [Fintype α₀] [Fintype α₁] in
private theorem joint2Atom_sum_snd (p : PMF (α₀ × α₁)) (W₀ : α₀ → PMF β₀)
    (W₁ : α₁ → PMF β₁) (x : α₀ × α₁) :
    ∑ y, joint2Atom p W₀ W₁ (x, y) = (p x).toReal := by
  classical
  rw [Fintype.sum_prod_type]
  calc ∑ y₀ : β₀, ∑ y₁ : β₁, joint2Atom p W₀ W₁ (x, (y₀, y₁))
      = (p x).toReal * ((∑ y₀, ((W₀ x.1) y₀).toReal) *
          (∑ y₁, ((W₁ x.2) y₁).toReal)) := by
        rw [Fintype.sum_mul_sum]
        simp only [joint2Atom, Finset.mul_sum, mul_assoc]
    _ = (p x).toReal := by
        rw [MathlibExt.InformationTheory.GallagerExponent.sum_toReal_eq_one,
          MathlibExt.InformationTheory.GallagerExponent.sum_toReal_eq_one, mul_one, mul_one]

private theorem joint2_fst_toReal (p : PMF (α₀ × α₁)) (W₀ : α₀ → PMF β₀)
    (W₁ : α₁ → PMF β₁) (x : α₀ × α₁) :
    (((joint2PMF p W₀ W₁).map Prod.fst) x).toReal = (p x).toReal := by
  rw [PMF.toReal_map_fst_apply]
  exact (Finset.sum_congr rfl fun y _ => joint2PMF_apply_toReal p W₀ W₁ (x, y)).trans
    (joint2Atom_sum_snd p W₀ W₁ x)

private theorem joint2_snd_toReal (p : PMF (α₀ × α₁)) (W₀ : α₀ → PMF β₀)
    (W₁ : α₁ → PMF β₁) (y : β₀ × β₁) :
    (((joint2PMF p W₀ W₁).map Prod.snd) y).toReal =
      ∑ x, joint2Atom p W₀ W₁ (x, y) := by
  rw [PMF.toReal_map_snd_apply]
  exact Finset.sum_congr rfl fun x _ => joint2PMF_apply_toReal p W₀ W₁ (x, y)

private theorem fiber0_toReal {α₀ α₁ β₀ β₁ : Type*} [Finite α₀] [Fintype α₁] [Finite β₀]
    [Fintype β₁] (p : PMF (α₀ × α₁)) (W₀ : α₀ → PMF β₀)
    (W₁ : α₁ → PMF β₁) (a : α₀) (b : β₀) :
    (∑ x₁, ∑ y₁, joint2Atom p W₀ W₁ ((a, x₁), (b, y₁))) =
      ((p.map Prod.fst) a).toReal * ((W₀ a) b).toReal := by
  classical
  let := Fintype.ofFinite β₀
  calc ∑ x₁, ∑ y₁, joint2Atom p W₀ W₁ ((a, x₁), (b, y₁))
      = ∑ x₁, ((W₀ a) b).toReal * (p (a, x₁)).toReal := by
        refine Finset.sum_congr rfl fun x₁ _ => ?_
        calc ∑ y₁, joint2Atom p W₀ W₁ ((a, x₁), (b, y₁))
            = ∑ y₁, ((p (a, x₁)).toReal * ((W₀ a) b).toReal) * ((W₁ x₁) y₁).toReal := by
              refine Finset.sum_congr rfl fun y₁ _ => ?_
              simp only [joint2Atom]
          _ = ((p (a, x₁)).toReal * ((W₀ a) b).toReal) *
              (∑ y₁, ((W₁ x₁) y₁).toReal) :=
            (Finset.mul_sum _ _ _).symm
          _ = ((W₀ a) b).toReal * (p (a, x₁)).toReal := by
              rw [MathlibExt.InformationTheory.GallagerExponent.sum_toReal_eq_one, mul_one]
              ring
    _ = ((W₀ a) b).toReal * ∑ x₁, (p (a, x₁)).toReal := by
        rw [Finset.mul_sum]
    _ = ((p.map Prod.fst) a).toReal * ((W₀ a) b).toReal := by
        rw [PMF.toReal_map_fst_apply]; ring

private theorem fiber1_toReal {α₀ α₁ β₀ β₁ : Type*} [Fintype α₀] [Finite α₁] [Fintype β₀]
    [Finite β₁] (p : PMF (α₀ × α₁)) (W₀ : α₀ → PMF β₀)
    (W₁ : α₁ → PMF β₁) (a : α₁) (b : β₁) :
    (∑ x₀, ∑ y₀, joint2Atom p W₀ W₁ ((x₀, a), (y₀, b))) =
      ((p.map Prod.snd) a).toReal * ((W₁ a) b).toReal := by
  classical
  let := Fintype.ofFinite β₁
  calc ∑ x₀, ∑ y₀, joint2Atom p W₀ W₁ ((x₀, a), (y₀, b))
      = ∑ x₀, ((W₁ a) b).toReal * (p (x₀, a)).toReal := by
        refine Finset.sum_congr rfl fun x₀ _ => ?_
        calc ∑ y₀, joint2Atom p W₀ W₁ ((x₀, a), (y₀, b))
            = ∑ y₀, ((W₁ a) b).toReal * ((p (x₀, a)).toReal * ((W₀ x₀) y₀).toReal) := by
              refine Finset.sum_congr rfl fun y₀ _ => ?_
              simp only [joint2Atom]; ring
          _ = ((W₁ a) b).toReal *
              (∑ y₀, (p (x₀, a)).toReal * ((W₀ x₀) y₀).toReal) :=
            (Finset.mul_sum _ _ _).symm
          _ = ((W₁ a) b).toReal * (p (x₀, a)).toReal := by
              have hsum : (∑ y₀, (p (x₀, a)).toReal * ((W₀ x₀) y₀).toReal) =
                  (p (x₀, a)).toReal := by
                rw [← Finset.mul_sum,
                  MathlibExt.InformationTheory.GallagerExponent.sum_toReal_eq_one, mul_one]
              rw [hsum]
    _ = ((W₁ a) b).toReal * ∑ x₀, (p (x₀, a)).toReal := by
        rw [Finset.mul_sum]
    _ = ((p.map Prod.snd) a).toReal * ((W₁ a) b).toReal := by
        rw [PMF.toReal_map_snd_apply]; ring

/-- Tensorization for two blocks: the mutual information of a two-block joint law is at most
the sum of the mutual informations of its two coordinate laws. -/
private theorem joint2_mutualInfo_le (p : PMF (α₀ × α₁)) (W₀ : α₀ → PMF β₀)
    (W₁ : α₁ → PMF β₁) :
    finiteMutualInformation (joint2PMF p W₀ W₁) ≤
      finiteMutualInformation ((p.map Prod.fst).bind fun a => (W₀ a).map (Prod.mk a)) +
        finiteMutualInformation ((p.map Prod.snd).bind fun a => (W₁ a).map (Prod.mk a)) := by
  classical
  have hswap0 : ∀ (F : α₀ → β₀ → α₁ → β₁ → ℝ),
      (∑ a, ∑ b, ∑ x₁, ∑ y₁, F a b x₁ y₁) = ∑ a, ∑ x₁, ∑ b, ∑ y₁, F a b x₁ y₁ :=
    fun F => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have hswap1 : ∀ (F : α₁ → β₁ → α₀ → β₀ → ℝ),
      (∑ a₁, ∑ b₁, ∑ x₀, ∑ y₀, F a₁ b₁ x₀ y₀) =
        ∑ x₀, ∑ a₁, ∑ y₀, ∑ b₁, F a₁ b₁ x₀ y₀ := by
    intro F
    calc ∑ a₁, ∑ b₁, ∑ x₀, ∑ y₀, F a₁ b₁ x₀ y₀
        = ∑ a₁, ∑ x₀, ∑ b₁, ∑ y₀, F a₁ b₁ x₀ y₀ :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ x₀, ∑ a₁, ∑ b₁, ∑ y₀, F a₁ b₁ x₀ y₀ := Finset.sum_comm
      _ = ∑ x₀, ∑ a₁, ∑ y₀, ∑ b₁, F a₁ b₁ x₀ y₀ :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have hJeq : finiteMutualInformation (joint2PMF p W₀ W₁) =
      (∑ t, joint2Atom p W₀ W₁ t * Real.log (joint2Atom p W₀ W₁ t /
        ((p t.1).toReal * (((joint2PMF p W₀ W₁).map Prod.snd) t.2).toReal))) / Real.log 2 := by
    rw [mutualInfo_sum]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [joint2PMF_apply_toReal, joint2_fst_toReal]
  have h0eq : finiteMutualInformation
      ((p.map Prod.fst).bind fun a => (W₀ a).map (Prod.mk a)) =
      (∑ a, ∑ x₁, ∑ b, ∑ y₁, joint2Atom p W₀ W₁ ((a, x₁), (b, y₁)) *
        Real.log ((((p.map Prod.fst) a).toReal * ((W₀ a) b).toReal) /
          (((p.map Prod.fst) a).toReal *
            (∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') b).toReal)))) / Real.log 2 := by
    rw [mutualInfo_sum]
    congr 1
    calc ∑ s, (((p.map Prod.fst).bind fun a => (W₀ a).map (Prod.mk a)) s).toReal *
          Real.log ((((p.map Prod.fst).bind fun a => (W₀ a).map (Prod.mk a)) s).toReal /
            (((((p.map Prod.fst).bind fun a => (W₀ a).map (Prod.mk a)).map Prod.fst) s.1).toReal *
              ((((p.map Prod.fst).bind fun a => (W₀ a).map (Prod.mk a)).map Prod.snd) s.2).toReal))
        = ∑ a, ∑ b, (((p.map Prod.fst) a).toReal * ((W₀ a) b).toReal) *
            Real.log ((((p.map Prod.fst) a).toReal * ((W₀ a) b).toReal) /
              (((p.map Prod.fst) a).toReal *
                (∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') b).toReal))) := by
          simp only [Fintype.sum_prod_type, bind_joint_apply_toReal, bind_fst_toReal,
            bind_snd_toReal]
      _ = ∑ a, ∑ b, ∑ x₁, ∑ y₁, joint2Atom p W₀ W₁ ((a, x₁), (b, y₁)) *
            Real.log ((((p.map Prod.fst) a).toReal * ((W₀ a) b).toReal) /
              (((p.map Prod.fst) a).toReal *
                (∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') b).toReal))) := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [← fiber0_toReal p W₀ W₁]
          simp_rw [Finset.sum_mul]
      _ = ∑ a, ∑ x₁, ∑ b, ∑ y₁, joint2Atom p W₀ W₁ ((a, x₁), (b, y₁)) *
            Real.log ((((p.map Prod.fst) a).toReal * ((W₀ a) b).toReal) /
              (((p.map Prod.fst) a).toReal *
                (∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') b).toReal))) := hswap0 _
  have h1eq : finiteMutualInformation
      ((p.map Prod.snd).bind fun a => (W₁ a).map (Prod.mk a)) =
      (∑ a, ∑ x₁, ∑ b, ∑ y₁, joint2Atom p W₀ W₁ ((a, x₁), (b, y₁)) *
        Real.log ((((p.map Prod.snd) x₁).toReal * ((W₁ x₁) y₁).toReal) /
          (((p.map Prod.snd) x₁).toReal *
            (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y₁).toReal)))) / Real.log 2 := by
    rw [mutualInfo_sum]
    congr 1
    calc ∑ s, (((p.map Prod.snd).bind fun a => (W₁ a).map (Prod.mk a)) s).toReal *
          Real.log ((((p.map Prod.snd).bind fun a => (W₁ a).map (Prod.mk a)) s).toReal /
            (((((p.map Prod.snd).bind fun a => (W₁ a).map (Prod.mk a)).map Prod.fst) s.1).toReal *
              ((((p.map Prod.snd).bind fun a => (W₁ a).map (Prod.mk a)).map Prod.snd) s.2).toReal))
        = ∑ a₁, ∑ b₁, (((p.map Prod.snd) a₁).toReal * ((W₁ a₁) b₁).toReal) *
            Real.log ((((p.map Prod.snd) a₁).toReal * ((W₁ a₁) b₁).toReal) /
              (((p.map Prod.snd) a₁).toReal *
                (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') b₁).toReal))) := by
          simp only [Fintype.sum_prod_type, bind_joint_apply_toReal, bind_fst_toReal,
            bind_snd_toReal]
      _ = ∑ a₁, ∑ b₁, ∑ x₀, ∑ y₀, joint2Atom p W₀ W₁ ((x₀, a₁), (y₀, b₁)) *
            Real.log ((((p.map Prod.snd) a₁).toReal * ((W₁ a₁) b₁).toReal) /
              (((p.map Prod.snd) a₁).toReal *
                (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') b₁).toReal))) := by
          refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun b₁ _ => ?_
          rw [← fiber1_toReal p W₀ W₁]
          simp_rw [Finset.sum_mul]
      _ = ∑ a, ∑ x₁, ∑ b, ∑ y₁, joint2Atom p W₀ W₁ ((a, x₁), (b, y₁)) *
            Real.log ((((p.map Prod.snd) x₁).toReal * ((W₁ x₁) y₁).toReal) /
              (((p.map Prod.snd) x₁).toReal *
                (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y₁).toReal))) := hswap1 _
  rw [hJeq, h0eq, h1eq, ← add_div]
  refine (div_le_div_iff_of_pos_right (Real.log_pos one_lt_two)).mpr ?_
  -- Pointwise log identity, on the support of the joint law.
  have hpoint : ∀ (a : α₀) (x₁ : α₁) (b : β₀) (y₁ : β₁),
      joint2Atom p W₀ W₁ ((a, x₁), (b, y₁)) *
        (Real.log ((((p.map Prod.fst) a).toReal * ((W₀ a) b).toReal) /
            (((p.map Prod.fst) a).toReal *
              (∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') b).toReal))) +
          Real.log ((((p.map Prod.snd) x₁).toReal * ((W₁ x₁) y₁).toReal) /
            (((p.map Prod.snd) x₁).toReal *
              (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y₁).toReal))) -
          Real.log (joint2Atom p W₀ W₁ ((a, x₁), (b, y₁)) /
            ((p (a, x₁)).toReal * (((joint2PMF p W₀ W₁).map Prod.snd) (b, y₁)).toReal)))
      = joint2Atom p W₀ W₁ ((a, x₁), (b, y₁)) *
        Real.log ((((joint2PMF p W₀ W₁).map Prod.snd) (b, y₁)).toReal /
          ((∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') b).toReal) *
            (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y₁).toReal))) := by
    intro a x₁ b y₁
    by_cases hJ : joint2Atom p W₀ W₁ ((a, x₁), (b, y₁)) = 0
    · simp [hJ]
    · have hJpos : 0 < joint2Atom p W₀ W₁ ((a, x₁), (b, y₁)) :=
        lt_of_le_of_ne (joint2Atom_nonneg p W₀ W₁ _) (Ne.symm hJ)
      have hJ' : 0 < (p (a, x₁)).toReal * ((W₀ a) b).toReal * ((W₁ x₁) y₁).toReal := hJpos
      have hp : 0 < (p (a, x₁)).toReal := by
        by_contra h
        have hz : (p (a, x₁)).toReal = 0 :=
          le_antisymm (le_of_not_gt h) ENNReal.toReal_nonneg
        rw [hz, zero_mul, zero_mul] at hJ'
        exact lt_irrefl _ hJ'
      have hw0 : 0 < ((W₀ a) b).toReal := by
        by_contra h
        have hz : ((W₀ a) b).toReal = 0 :=
          le_antisymm (le_of_not_gt h) ENNReal.toReal_nonneg
        rw [hz, mul_zero, zero_mul] at hJ'
        exact lt_irrefl _ hJ'
      have hw1 : 0 < ((W₁ x₁) y₁).toReal := by
        by_contra h
        have hz : ((W₁ x₁) y₁).toReal = 0 :=
          le_antisymm (le_of_not_gt h) ENNReal.toReal_nonneg
        rw [hz, mul_zero] at hJ'
        exact lt_irrefl _ hJ'
      have hJ0atom : 0 < ((p.map Prod.fst) a).toReal * ((W₀ a) b).toReal := by
        have hfib := fiber0_toReal p W₀ W₁ a b
        have hle : joint2Atom p W₀ W₁ ((a, x₁), (b, y₁)) ≤
            ∑ x₁', ∑ y₁', joint2Atom p W₀ W₁ ((a, x₁'), (b, y₁')) :=
          le_trans
            (Finset.single_le_sum (fun y₁' _ =>
              joint2Atom_nonneg p W₀ W₁ ((a, x₁), (b, y₁'))) (Finset.mem_univ y₁))
            (Finset.single_le_sum (fun x₁' _ => Finset.sum_nonneg fun y₁' _ =>
              joint2Atom_nonneg p W₀ W₁ ((a, x₁'), (b, y₁'))) (Finset.mem_univ x₁))
        rw [hfib] at hle
        exact hJpos.trans_le hle
      have hJ1atom : 0 < ((p.map Prod.snd) x₁).toReal * ((W₁ x₁) y₁).toReal := by
        have hfib := fiber1_toReal p W₀ W₁ x₁ y₁
        have hle : joint2Atom p W₀ W₁ ((a, x₁), (b, y₁)) ≤
            ∑ x₀, ∑ y₀, joint2Atom p W₀ W₁ ((x₀, x₁), (y₀, y₁)) :=
          le_trans
            (Finset.single_le_sum (fun y₀ _ =>
              joint2Atom_nonneg p W₀ W₁ ((a, x₁), (y₀, y₁))) (Finset.mem_univ b))
            (Finset.single_le_sum (fun x₀ _ => Finset.sum_nonneg fun y₀ _ =>
              joint2Atom_nonneg p W₀ W₁ ((x₀, x₁), (y₀, y₁))) (Finset.mem_univ a))
        rw [hfib] at hle
        exact hJpos.trans_le hle
      have hJ0fst : 0 < ((p.map Prod.fst) a).toReal := by
        rw [PMF.toReal_map_fst_apply]
        refine lt_of_lt_of_le hp ?_
        exact Finset.single_le_sum (f := fun b => (p (a, b)).toReal)
          (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ x₁)
      have hJ1fst : 0 < ((p.map Prod.snd) x₁).toReal := by
        rw [PMF.toReal_map_snd_apply]
        refine lt_of_lt_of_le hp ?_
        exact Finset.single_le_sum (f := fun a' => (p (a', x₁)).toReal)
          (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ a)
      have hJ0snd : 0 < ∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') b).toReal :=
        lt_of_lt_of_le hJ0atom
          (Finset.single_le_sum
            (f := fun a' => ((p.map Prod.fst) a').toReal * ((W₀ a') b).toReal)
            (fun _ _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
            (Finset.mem_univ a))
      have hJ1snd : 0 < ∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y₁).toReal :=
        lt_of_lt_of_le hJ1atom
          (Finset.single_le_sum
            (f := fun a' => ((p.map Prod.snd) a').toReal * ((W₁ a') y₁).toReal)
            (fun _ _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
            (Finset.mem_univ x₁))
      have hYsnd : 0 < (((joint2PMF p W₀ W₁).map Prod.snd) (b, y₁)).toReal := by
        rw [joint2_snd_toReal]
        refine lt_of_lt_of_le hJpos ?_
        exact Finset.single_le_sum (fun x _ => joint2Atom_nonneg p W₀ W₁ (x, (b, y₁)))
          (Finset.mem_univ (a, x₁))
      have hAne : ((((p.map Prod.fst) a).toReal * ((W₀ a) b).toReal) /
          (((p.map Prod.fst) a).toReal *
            (∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') b).toReal))) ≠ 0 :=
        div_ne_zero hJ0atom.ne' (mul_ne_zero hJ0fst.ne' hJ0snd.ne')
      have hBne : ((((p.map Prod.snd) x₁).toReal * ((W₁ x₁) y₁).toReal) /
          (((p.map Prod.snd) x₁).toReal *
            (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y₁).toReal))) ≠ 0 :=
        div_ne_zero hJ1atom.ne' (mul_ne_zero hJ1fst.ne' hJ1snd.ne')
      have hCne : (joint2Atom p W₀ W₁ ((a, x₁), (b, y₁)) /
          ((p (a, x₁)).toReal * (((joint2PMF p W₀ W₁).map Prod.snd) (b, y₁)).toReal)) ≠ 0 :=
        div_ne_zero hJpos.ne' (mul_ne_zero hp.ne' hYsnd.ne')
      have harg : ((((p.map Prod.fst) a).toReal * ((W₀ a) b).toReal) /
            (((p.map Prod.fst) a).toReal *
              (∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') b).toReal))) *
          ((((p.map Prod.snd) x₁).toReal * ((W₁ x₁) y₁).toReal) /
            (((p.map Prod.snd) x₁).toReal *
              (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y₁).toReal))) /
          (joint2Atom p W₀ W₁ ((a, x₁), (b, y₁)) /
            ((p (a, x₁)).toReal * (((joint2PMF p W₀ W₁).map Prod.snd) (b, y₁)).toReal))
        = (((joint2PMF p W₀ W₁).map Prod.snd) (b, y₁)).toReal /
          ((∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') b).toReal) *
            (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y₁).toReal)) := by
        have hfacJ : joint2Atom p W₀ W₁ ((a, x₁), (b, y₁)) =
            (p (a, x₁)).toReal * ((W₀ a) b).toReal * ((W₁ x₁) y₁).toReal := rfl
        rw [hfacJ]
        field_simp
      calc joint2Atom p W₀ W₁ ((a, x₁), (b, y₁)) *
            (Real.log _ + Real.log _ - Real.log _)
          = joint2Atom p W₀ W₁ ((a, x₁), (b, y₁)) *
              Real.log (((((p.map Prod.fst) a).toReal * ((W₀ a) b).toReal) /
                (((p.map Prod.fst) a).toReal *
                  (∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') b).toReal))) *
                ((((p.map Prod.snd) x₁).toReal * ((W₁ x₁) y₁).toReal) /
                (((p.map Prod.snd) x₁).toReal *
                  (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y₁).toReal))) /
              (joint2Atom p W₀ W₁ ((a, x₁), (b, y₁)) /
                ((p (a, x₁)).toReal * (((joint2PMF p W₀ W₁).map Prod.snd) (b, y₁)).toReal))) := by
            rw [← Real.log_mul hAne hBne, ← Real.log_div (mul_ne_zero hAne hBne) hCne]
        _ = joint2Atom p W₀ W₁ ((a, x₁), (b, y₁)) *
              Real.log ((((joint2PMF p W₀ W₁).map Prod.snd) (b, y₁)).toReal /
                ((∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') b).toReal) *
                  (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y₁).toReal))) := by
            rw [harg]
  -- The difference of the two sides is a KL-type sum, hence nonnegative.
  have hle0 : ∀ (b : β₀) (y₁ : β₁),
      (((joint2PMF p W₀ W₁).map Prod.snd) (b, y₁)).toReal ≤
        ∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') b).toReal := by
    intro b y₁
    have hY0 : (∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') b).toReal) =
        ∑ a, ∑ x₁, ∑ y₁', joint2Atom p W₀ W₁ ((a, x₁), (b, y₁')) :=
      Finset.sum_congr rfl fun a' _ => (fiber0_toReal p W₀ W₁ a' b).symm
    rw [joint2_snd_toReal, Fintype.sum_prod_type, hY0]
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun x₁ _ => ?_
    exact Finset.single_le_sum (fun y₁' _ =>
      joint2Atom_nonneg p W₀ W₁ ((a, x₁), (b, y₁'))) (Finset.mem_univ y₁)
  have hle1 : ∀ (b : β₀) (y₁ : β₁),
      (((joint2PMF p W₀ W₁).map Prod.snd) (b, y₁)).toReal ≤
        ∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y₁).toReal := by
    intro b y₁
    have hY1 : (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y₁).toReal) =
        ∑ x₀, ∑ a', ∑ y₀, joint2Atom p W₀ W₁ ((x₀, a'), (y₀, y₁)) := by
      calc (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y₁).toReal)
          = ∑ a', ∑ x₀, ∑ y₀, joint2Atom p W₀ W₁ ((x₀, a'), (y₀, y₁)) :=
            Finset.sum_congr rfl fun a' _ => (fiber1_toReal p W₀ W₁ a' y₁).symm
        _ = ∑ x₀, ∑ a', ∑ y₀, joint2Atom p W₀ W₁ ((x₀, a'), (y₀, y₁)) :=
            Finset.sum_comm
    rw [joint2_snd_toReal, Fintype.sum_prod_type, hY1]
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun x₁ _ => ?_
    exact Finset.single_le_sum (fun y₀ _ =>
      joint2Atom_nonneg p W₀ W₁ ((a, x₁), (y₀, y₁))) (Finset.mem_univ b)
  have hRzero : ∀ y : β₀ × β₁,
      (∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') y.1).toReal) *
        (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y.2).toReal) = 0 →
      (((joint2PMF p W₀ W₁).map Prod.snd) y).toReal = 0 := by
    intro y hy
    rcases mul_eq_zero.mp hy with h0 | h1
    · exact le_antisymm ((hle0 y.1 y.2).trans h0.le) ENNReal.toReal_nonneg
    · exact le_antisymm ((hle1 y.1 y.2).trans h1.le) ENNReal.toReal_nonneg
  have hsumY : ∑ y : β₀ × β₁, (((joint2PMF p W₀ W₁).map Prod.snd) y).toReal = 1 :=
    MathlibExt.InformationTheory.GallagerExponent.sum_toReal_eq_one _
  have hsumY0 : ∑ b : β₀, (∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') b).toReal) = 1 := by
    calc ∑ b : β₀, (∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') b).toReal)
        = ∑ a', ((p.map Prod.fst) a').toReal * (∑ b, ((W₀ a') b).toReal) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun a' _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ a', ((p.map Prod.fst) a').toReal :=
          Finset.sum_congr rfl fun a' _ => by
            rw [MathlibExt.InformationTheory.GallagerExponent.sum_toReal_eq_one, mul_one]
      _ = 1 := MathlibExt.InformationTheory.GallagerExponent.sum_toReal_eq_one _
  have hsumY1 : ∑ y₁ : β₁, (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y₁).toReal) = 1 := by
    calc ∑ y₁ : β₁, (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y₁).toReal)
        = ∑ a', ((p.map Prod.snd) a').toReal * (∑ y₁, ((W₁ a') y₁).toReal) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun a' _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ a', ((p.map Prod.snd) a').toReal :=
          Finset.sum_congr rfl fun a' _ => by
            rw [MathlibExt.InformationTheory.GallagerExponent.sum_toReal_eq_one, mul_one]
      _ = 1 := MathlibExt.InformationTheory.GallagerExponent.sum_toReal_eq_one _
  have hsumR : ∑ y : β₀ × β₁,
      (∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') y.1).toReal) *
        (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y.2).toReal) = 1 := by
    rw [Fintype.sum_prod_type]
    change (∑ x : β₀, ∑ y : β₁, (∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') x).toReal) *
        (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y).toReal)) = 1
    rw [← Fintype.sum_mul_sum, hsumY0, hsumY1, mul_one]
  have hreorder : ∀ (F : α₀ → α₁ → β₀ → β₁ → ℝ),
      (∑ a, ∑ x₁, ∑ b, ∑ y₁, F a x₁ b y₁) = ∑ b, ∑ y₁, ∑ a, ∑ x₁, F a x₁ b y₁ := by
    intro F
    calc ∑ a, ∑ x₁, ∑ b, ∑ y₁, F a x₁ b y₁
        = ∑ a, ∑ b, ∑ x₁, ∑ y₁, F a x₁ b y₁ :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ b, ∑ a, ∑ x₁, ∑ y₁, F a x₁ b y₁ := Finset.sum_comm
      _ = ∑ b, ∑ y₁, ∑ a, ∑ x₁, F a x₁ b y₁ := by
          refine Finset.sum_congr rfl fun b _ => ?_
          calc ∑ a, ∑ x₁, ∑ y₁, F a x₁ b y₁
              = ∑ a, ∑ y₁, ∑ x₁, F a x₁ b y₁ :=
                Finset.sum_congr rfl fun _ _ => Finset.sum_comm
            _ = ∑ y₁, ∑ a, ∑ x₁, F a x₁ b y₁ := Finset.sum_comm
  have hcollapse : (∑ a, ∑ x₁, ∑ b, ∑ y₁, joint2Atom p W₀ W₁ ((a, x₁), (b, y₁)) *
        Real.log ((((joint2PMF p W₀ W₁).map Prod.snd) (b, y₁)).toReal /
          ((∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') b).toReal) *
            (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y₁).toReal))))
      = ∑ y : β₀ × β₁, (((joint2PMF p W₀ W₁).map Prod.snd) y).toReal *
          Real.log ((((joint2PMF p W₀ W₁).map Prod.snd) y).toReal /
            ((∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') y.1).toReal) *
              (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y.2).toReal))) := by
    rw [hreorder, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun y₁ _ => ?_
    have hfib : (∑ a, ∑ x₁, joint2Atom p W₀ W₁ ((a, x₁), (b, y₁))) =
        (((joint2PMF p W₀ W₁).map Prod.snd) (b, y₁)).toReal := by
      rw [joint2_snd_toReal, Fintype.sum_prod_type]
    simp_rw [← Finset.sum_mul, hfib]
  have hnonneg : 0 ≤ ∑ y : β₀ × β₁, (((joint2PMF p W₀ W₁).map Prod.snd) y).toReal *
      Real.log ((((joint2PMF p W₀ W₁).map Prod.snd) y).toReal /
        ((∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') y.1).toReal) *
          (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y.2).toReal))) := by
    classical
    set S : Finset (β₀ × β₁) := Finset.univ.filter fun y =>
      (∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') y.1).toReal) *
        (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y.2).toReal) ≠ 0 with hS
    have hlogsum := Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div S
      (fun y => (((joint2PMF p W₀ W₁).map Prod.snd) y).toReal)
      (fun y => (∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') y.1).toReal) *
        (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y.2).toReal))
      (fun y _ => ENNReal.toReal_nonneg)
      (fun y hy => by
        have hnn : 0 ≤ (∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') y.1).toReal) *
            (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y.2).toReal) :=
          mul_nonneg (Finset.sum_nonneg fun a' _ => mul_nonneg ENNReal.toReal_nonneg
            ENNReal.toReal_nonneg) (Finset.sum_nonneg fun a' _ => mul_nonneg
            ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
        rcases hnn.eq_or_lt with h | h
        · exact absurd h.symm (Finset.mem_filter.mp hy).2
        · exact h)
    have hSsumY : ∑ y ∈ S, (((joint2PMF p W₀ W₁).map Prod.snd) y).toReal = 1 := by
      rw [← hsumY]
      refine Finset.sum_subset (Finset.filter_subset _ _) fun y _ hy => ?_
      have hy0 : (∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') y.1).toReal) *
          (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y.2).toReal) = 0 := by
        by_contra hne
        exact hy (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hne⟩)
      rw [hRzero y hy0]
    have hSsumR : ∑ y ∈ S, (∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') y.1).toReal) *
        (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y.2).toReal) = 1 := by
      rw [← hsumR]
      refine Finset.sum_subset (Finset.filter_subset _ _) fun y _ hy => ?_
      have hy0 : (∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') y.1).toReal) *
          (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y.2).toReal) = 0 := by
        by_contra hne
        exact hy (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hne⟩)
      rw [hy0]
    have hterm : (∑ y ∈ S, (((joint2PMF p W₀ W₁).map Prod.snd) y).toReal *
        Real.log ((((joint2PMF p W₀ W₁).map Prod.snd) y).toReal /
          ((∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') y.1).toReal) *
            (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y.2).toReal))))
        = ∑ y : β₀ × β₁, (((joint2PMF p W₀ W₁).map Prod.snd) y).toReal *
          Real.log ((((joint2PMF p W₀ W₁).map Prod.snd) y).toReal /
            ((∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') y.1).toReal) *
              (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y.2).toReal))) := by
      refine Finset.sum_subset (Finset.filter_subset _ _) fun y _ hy => ?_
      have hy0 : (∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') y.1).toReal) *
          (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y.2).toReal) = 0 := by
        by_contra hne
        exact hy (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hne⟩)
      rw [hRzero y hy0]
      simp
    rw [hSsumY, hSsumR, div_one, Real.log_one, one_mul] at hlogsum
    rw [← hterm]
    exact hlogsum
  have hdiff : (∑ a, ∑ x₁, ∑ b, ∑ y₁, joint2Atom p W₀ W₁ ((a, x₁), (b, y₁)) *
        Real.log ((((p.map Prod.fst) a).toReal * ((W₀ a) b).toReal) /
          (((p.map Prod.fst) a).toReal *
            (∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') b).toReal)))) +
      (∑ a, ∑ x₁, ∑ b, ∑ y₁, joint2Atom p W₀ W₁ ((a, x₁), (b, y₁)) *
        Real.log ((((p.map Prod.snd) x₁).toReal * ((W₁ x₁) y₁).toReal) /
          (((p.map Prod.snd) x₁).toReal *
            (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y₁).toReal)))) -
      (∑ t, joint2Atom p W₀ W₁ t * Real.log (joint2Atom p W₀ W₁ t /
        ((p t.1).toReal * (((joint2PMF p W₀ W₁).map Prod.snd) t.2).toReal)))
      = ∑ a, ∑ x₁, ∑ b, ∑ y₁, joint2Atom p W₀ W₁ ((a, x₁), (b, y₁)) *
          Real.log ((((joint2PMF p W₀ W₁).map Prod.snd) (b, y₁)).toReal /
            ((∑ a', ((p.map Prod.fst) a').toReal * ((W₀ a') b).toReal) *
              (∑ a', ((p.map Prod.snd) a').toReal * ((W₁ a') y₁).toReal))) := by
    have h4 : (∑ t, joint2Atom p W₀ W₁ t * Real.log (joint2Atom p W₀ W₁ t /
        ((p t.1).toReal * (((joint2PMF p W₀ W₁).map Prod.snd) t.2).toReal)))
        = ∑ a, ∑ x₁, ∑ b, ∑ y₁, joint2Atom p W₀ W₁ ((a, x₁), (b, y₁)) *
            Real.log (joint2Atom p W₀ W₁ ((a, x₁), (b, y₁)) /
              ((p (a, x₁)).toReal * (((joint2PMF p W₀ W₁).map Prod.snd) (b, y₁)).toReal)) := by
      simp only [Fintype.sum_prod_type]
    rw [h4]
    simp_rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x₁ _ =>
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun y₁ _ => ?_
    rw [← hpoint a x₁ b y₁]
    ring
  rw [hcollapse] at hdiff
  linarith [hdiff, hnonneg]

end

/-- If the channel input is a deterministic function of the message, the mutual
information with the output is unchanged. -/
private theorem finiteMutualInformation_bind_map_eq {δ α β : Type*} [Finite δ] [Finite α]
    [Finite β] (r : PMF δ) (h : δ → α) (W : α → PMF β) :
    finiteMutualInformation (r.bind fun d => (W (h d)).map (Prod.mk d)) =
      finiteMutualInformation ((r.map h).bind fun a => (W a).map (Prod.mk a)) := by
  classical
  let := Fintype.ofFinite δ
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  have hY : ∀ b : β, (∑ d, (r d).toReal * ((W (h d)) b).toReal) =
      ∑ a, ((r.map h) a).toReal * ((W a) b).toReal := by
    intro b
    simp_rw [map_apply_toReal, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [ite_mul, zero_mul]
    have hsingle : (∑ x, if h d = x then (r d).toReal * ((W x) b).toReal else 0) =
        (r d).toReal * ((W (h d)) b).toReal := by
      rw [Finset.sum_eq_single (h d)]
      · simp
      · intro x _ hx; exact ite_eq_right (Ne.symm hx)
      · intro hcon; simp at hcon
    exact hsingle.symm
  rw [mutualInfo_sum, mutualInfo_sum]
  congr 1
  simp only [Fintype.sum_prod_type, bind_joint_apply_toReal, bind_fst_toReal, bind_snd_toReal]
  simp only [hY]
  have hgroup : ∀ (F : δ → ℝ), (∑ d, F d) =
      ∑ a, ∑ d, if h d = a then F d else 0 := by
    intro F
    have hswap : (∑ a, ∑ d, if h d = a then F d else 0) =
        ∑ d, ∑ a, if h d = a then F d else 0 := Finset.sum_comm
    rw [hswap]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hsingle : (∑ a, if h d = a then F d else 0) = F d := by
      rw [Finset.sum_eq_single (h d)]
      · simp
      · intro x _ hx; exact ite_eq_right (Ne.symm hx)
      · intro hcon; simp at hcon
    exact hsingle.symm
  have hterm : ∀ (d : δ) (b : β),
      (r d).toReal * ((W (h d)) b).toReal *
        Real.log (((r d).toReal * ((W (h d)) b).toReal) /
          ((r d).toReal * (∑ a, ((r.map h) a).toReal * ((W a) b).toReal)))
      = (r d).toReal * ((W (h d)) b).toReal *
        Real.log (((W (h d)) b).toReal /
          (∑ a, ((r.map h) a).toReal * ((W a) b).toReal)) := by
    intro d b
    by_cases hr : (r d).toReal = 0
    · simp [hr]
    · by_cases hw : ((W (h d)) b).toReal = 0
      · simp [hw]
      · have hYpos : (∑ a, ((r.map h) a).toReal * ((W a) b).toReal) ≠ 0 := by
          rw [← hY, ← bind_snd_toReal]
          rw [bind_snd_toReal]
          have hle : (r d).toReal * ((W (h d)) b).toReal ≤
              ∑ d', (r d').toReal * ((W (h d')) b).toReal :=
            Finset.single_le_sum
              (f := fun d' => (r d').toReal * ((W (h d')) b).toReal)
              (fun _ _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
              (Finset.mem_univ d)
          have hpos : 0 < (r d).toReal * ((W (h d)) b).toReal :=
            mul_pos (lt_of_le_of_ne' ENNReal.toReal_nonneg hr)
              (lt_of_le_of_ne' ENNReal.toReal_nonneg hw)
          exact ne_of_gt (lt_of_lt_of_le hpos hle)
        rw [mul_div_mul_left _ _ hr]
  have hpush : ∀ (a : α) (G : δ → β → ℝ),
      (∑ d, if h d = a then (∑ b, G d b) else 0) =
        ∑ b, ∑ d, if h d = a then G d b else 0 := by
    intro a G
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hc : h d = a <;> simp [hc]
  have hgroupterm : ∀ (a : α) (b : β),
      (∑ d, if h d = a then (r d).toReal * ((W (h d)) b).toReal *
        Real.log (((r d).toReal * ((W (h d)) b).toReal) /
          ((r d).toReal * (∑ a', ((r.map h) a').toReal * ((W a') b).toReal))) else 0)
      = ((r.map h) a).toReal * ((W a) b).toReal *
        Real.log ((((r.map h) a).toReal * ((W a) b).toReal) /
          (((r.map h) a).toReal * (∑ a', ((r.map h) a').toReal * ((W a') b).toReal))) := by
    intro a b
    have h1 : (∑ d, if h d = a then (r d).toReal * ((W (h d)) b).toReal *
        Real.log (((r d).toReal * ((W (h d)) b).toReal) /
          ((r d).toReal * (∑ a', ((r.map h) a').toReal * ((W a') b).toReal))) else 0)
        = (∑ d, if h d = a then (r d).toReal else 0) *
          (((W a) b).toReal * Real.log (((W a) b).toReal /
            (∑ a', ((r.map h) a').toReal * ((W a') b).toReal))) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun d _ => ?_
      by_cases hd : h d = a
      · subst hd
        rw [ite_eq_left rfl, ite_eq_left rfl, hterm]
        ring
      · simp [hd]
    have h2 : ((r.map h) a).toReal * ((W a) b).toReal *
        Real.log ((((r.map h) a).toReal * ((W a) b).toReal) /
          (((r.map h) a).toReal * (∑ a', ((r.map h) a').toReal * ((W a') b).toReal)))
        = ((r.map h) a).toReal *
          (((W a) b).toReal * Real.log (((W a) b).toReal /
            (∑ a', ((r.map h) a').toReal * ((W a') b).toReal))) := by
      by_cases hq : ((r.map h) a).toReal = 0
      · rw [hq]; simp
      · rw [mul_div_mul_left _ _ hq]
        ring
    rw [h1, h2, map_apply_toReal]
  calc ∑ d, ∑ b, (r d).toReal * ((W (h d)) b).toReal *
        Real.log (((r d).toReal * ((W (h d)) b).toReal) /
          ((r d).toReal * (∑ a, ((r.map h) a).toReal * ((W a) b).toReal)))
      = ∑ a, ∑ b, (∑ d, if h d = a then (r d).toReal * ((W (h d)) b).toReal *
          Real.log (((r d).toReal * ((W (h d)) b).toReal) /
            ((r d).toReal * (∑ a', ((r.map h) a').toReal * ((W a') b).toReal))) else 0) := by
        refine (hgroup _).trans (Finset.sum_congr rfl fun a _ => hpush a _)
    _ = ∑ a, ∑ b, ((r.map h) a).toReal * ((W a) b).toReal *
        Real.log ((((r.map h) a).toReal * ((W a) b).toReal) /
          (((r.map h) a).toReal * (∑ a', ((r.map h) a').toReal * ((W a') b).toReal))) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hgroupterm a b

/-- Fano's inequality in the form needed for the weak converse: the conditional
entropy of the message given the decoded message is at most the binary entropy
of the error probability plus the error probability times `log M`. Here the
inequality is in nats, with the error probability written as a sum over the
off-diagonal atoms of the joint law of message and decoded message. -/
private theorem fano_bound_nats {M : ℕ} (hM : 2 ≤ M) (r : PMF (Fin M × Fin M))
    (huni : ∀ m, ((r.map Prod.fst) m).toReal = (M : ℝ)⁻¹) :
    (1 - ∑ j, ∑ m ∈ Finset.univ.erase j, (r (m, j)).toReal) * Real.log M ≤
      (∑ t, (r t).toReal * Real.log ((r t).toReal /
        (((r.map Prod.fst) t.1).toReal * ((r.map Prod.snd) t.2).toReal))) +
        Real.binEntropy (∑ j, ∑ m ∈ Finset.univ.erase j, (r (m, j)).toReal) := by
  classical
  set Pe : ℝ := ∑ j, ∑ m ∈ Finset.univ.erase j, (r (m, j)).toReal with hPe
  have hMpos : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le zero_lt_two hM
  have hlogM1 : (0 : ℝ) ≤ Real.log ((M - 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    have h1m : (1 : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ M - 1 by omega)
    exact h1m
  -- Per-symbol bound.
  have hper : ∀ j : Fin M,
      -(∑ m, (r (m, j)).toReal * Real.log ((r (m, j)).toReal /
        (((r.map Prod.snd) j).toReal)))
      ≤ (((r.map Prod.snd) j).toReal) *
          Real.binEntropy ((∑ m ∈ Finset.univ.erase j, (r (m, j)).toReal) /
            ((r.map Prod.snd) j).toReal) +
        (∑ m ∈ Finset.univ.erase j, (r (m, j)).toReal) *
          Real.log ((M - 1 : ℕ) : ℝ) := by
    intro j
    set w : ℝ := ((r.map Prod.snd) j).toReal with hw
    set e : ℝ := ∑ m ∈ Finset.univ.erase j, (r (m, j)).toReal with he
    set c : ℝ := (r (j, j)).toReal with hc
    have hw_nonneg : 0 ≤ w := ENNReal.toReal_nonneg
    have he_nonneg : 0 ≤ e :=
      Finset.sum_nonneg fun m _ => ENNReal.toReal_nonneg
    have hsum : ∑ m, (r (m, j)).toReal = w := by
      rw [hw, PMF.toReal_map_snd_apply]
    have hce : c + e = w := by
      rw [← hsum]
      rw [← Finset.add_sum_erase Finset.univ (fun m => (r (m, j)).toReal)
        (Finset.mem_univ j)]
    have hc_nonneg : 0 ≤ c := ENNReal.toReal_nonneg
    have hcle : c ≤ w := by
      rw [← hce]
      exact le_add_of_nonneg_right he_nonneg
    have hrle : ∀ m, (r (m, j)).toReal ≤ w := fun m => by
      rw [← hsum]
      exact Finset.single_le_sum (f := fun m' => (r (m', j)).toReal)
        (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ m)
    have he_le : e ≤ w := by
      rw [← hce]
      exact le_add_of_nonneg_left ENNReal.toReal_nonneg
    -- Expansion of the per-symbol conditional entropy.
    have hexpand : -(∑ m, (r (m, j)).toReal * Real.log ((r (m, j)).toReal / w))
        = -c * Real.log c - (∑ m ∈ Finset.univ.erase j,
            (r (m, j)).toReal * Real.log (r (m, j)).toReal) + w * Real.log w := by
      have hsplit : (∑ m, (r (m, j)).toReal * Real.log ((r (m, j)).toReal / w))
          = c * Real.log (c / w) +
            ∑ m ∈ Finset.univ.erase j, (r (m, j)).toReal * Real.log ((r (m, j)).toReal / w) := by
        rw [← Finset.add_sum_erase Finset.univ
          (fun m => (r (m, j)).toReal * Real.log ((r (m, j)).toReal / w)) (Finset.mem_univ j)]
      have hdiv : ∀ m, (r (m, j)).toReal * Real.log ((r (m, j)).toReal / w)
          = (r (m, j)).toReal * Real.log (r (m, j)).toReal -
            (r (m, j)).toReal * Real.log w := by
        intro m
        by_cases hm : (r (m, j)).toReal = 0
        · simp [hm]
        · rw [Real.log_div hm (ne_of_gt (lt_of_lt_of_le
            (lt_of_le_of_ne' ENNReal.toReal_nonneg hm) (hrle m)))]
          ring
      rw [hsplit]
      have hsumdiv : (∑ m ∈ Finset.univ.erase j,
          (r (m, j)).toReal * Real.log ((r (m, j)).toReal / w))
          = (∑ m ∈ Finset.univ.erase j, (r (m, j)).toReal * Real.log (r (m, j)).toReal) -
            e * Real.log w := by
        rw [Finset.sum_congr rfl fun m _ => hdiv m, Finset.sum_sub_distrib,
          ← Finset.sum_mul, he]
      rw [hsumdiv]
      have hcj : c * Real.log (c / w) = c * Real.log c - c * Real.log w := by
        by_cases hc0 : c = 0
        · simp [hc0]
        · rw [Real.log_div hc0 (ne_of_gt (lt_of_lt_of_le
            (lt_of_le_of_ne' hc_nonneg hc0) hcle))]
          ring
      rw [hcj]
      have hcw : c * Real.log w + e * Real.log w = w * Real.log w := by
        rw [← add_mul, hce]
      linarith [hcw]
    have hM1pos : (0 : ℝ) < ((M - 1 : ℕ) : ℝ) := by
      have h1m : (1 : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ M - 1 by omega)
      linarith
    have hcard : (∑ _m ∈ Finset.univ.erase j, (1 : ℝ)) = ((M - 1 : ℕ) : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ j),
        Finset.card_univ, Fintype.card_fin, mul_one]
    have hlogsum := Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div
      (Finset.univ.erase j) (fun m => (r (m, j)).toReal) (fun _ => (1 : ℝ))
      (fun m _ => ENNReal.toReal_nonneg) (fun _ _ => one_pos)
    rw [hcard] at hlogsum
    simp only [div_one] at hlogsum
    by_cases hw0 : w = 0
    · have hr0 : ∀ m, (r (m, j)).toReal = 0 := fun m =>
        le_antisymm ((hrle m).trans hw0.le) ENNReal.toReal_nonneg
      have he0 : e = 0 := by
        rw [he]
        exact Finset.sum_eq_zero fun m _ => hr0 m
      have hc0 : c = 0 := hr0 j
      rw [hexpand]
      have hS0 : (∑ m ∈ Finset.univ.erase j,
          (r (m, j)).toReal * Real.log (r (m, j)).toReal) = 0 :=
        Finset.sum_eq_zero fun m _ => by simp [hr0 m]
      rw [hS0, he0, hc0, hw0]
      simp
    · by_cases he0 : e = 0
      · have hcw2 : c = w := by rw [← hce, he0, add_zero]
        rw [hexpand]
        have hsum0 : (∑ m ∈ Finset.univ.erase j,
            (r (m, j)).toReal * Real.log (r (m, j)).toReal) = 0 := by
          apply Finset.sum_eq_zero
          intro m hm
          have hz : (r (m, j)).toReal = 0 := by
            have hle : (r (m, j)).toReal ≤ e :=
              Finset.single_le_sum (f := fun m' => (r (m', j)).toReal)
                (fun _ _ => ENNReal.toReal_nonneg) hm
            exact le_antisymm (hle.trans he0.le) ENNReal.toReal_nonneg
          simp [hz]
        rw [hsum0, hcw2, he0]
        simp only [zero_div, Real.binEntropy_zero, zero_mul, add_zero, sub_zero]
        linarith
      · by_cases hc0 : c = 0
        · have hew : e = w := by rw [← hce, hc0, zero_add]
          rw [hexpand]
          simp only [hc0, zero_mul, neg_zero, zero_sub]
          rw [← he] at hlogsum
          rw [hew] at hlogsum ⊢
          rw [div_self hw0, Real.binEntropy_one, mul_zero, zero_add]
          rw [Real.log_div (ne_of_gt (lt_of_le_of_ne' hw_nonneg hw0))
            (ne_of_gt hM1pos), mul_sub] at hlogsum
          linarith [hlogsum]
        · have hepos : 0 < e := lt_of_le_of_ne' he_nonneg he0
          have hcpos : 0 < c := lt_of_le_of_ne' hc_nonneg hc0
          have hwpos : 0 < w := lt_of_le_of_ne' hw_nonneg hw0
          have hbin : w * Real.binEntropy (e / w) =
              -e * Real.log e - c * Real.log c + w * Real.log w := by
            have h1 : 1 - e / w = c / w := by
              rw [eq_div_iff hwpos.ne']
              rw [sub_mul, one_mul, div_mul_cancel₀ _ hwpos.ne']
              linarith [hce]
            rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, h1]
            simp only [Real.negMulLog]
            rw [Real.log_div hepos.ne' hwpos.ne', Real.log_div hcpos.ne' hwpos.ne']
            field_simp
            linear_combination hce * Real.log w
          rw [hexpand, hbin]
          rw [← he] at hlogsum
          rw [Real.log_div hepos.ne' (ne_of_gt hM1pos), mul_sub] at hlogsum
          linarith [hlogsum]
  -- Sum the per-symbol bounds and apply Jensen's inequality.
  have hsumw : ∑ j : Fin M, ((r.map Prod.snd) j).toReal = 1 :=
    MathlibExt.InformationTheory.GallagerExponent.sum_toReal_eq_one _
  have hJensen : (∑ j : Fin M, ((r.map Prod.snd) j).toReal *
      Real.binEntropy ((∑ m ∈ Finset.univ.erase j, (r (m, j)).toReal) /
        ((r.map Prod.snd) j).toReal)) ≤ Real.binEntropy Pe := by
    have hwe : (∑ j : Fin M, ((r.map Prod.snd) j).toReal •
        ((∑ m ∈ Finset.univ.erase j, (r (m, j)).toReal) /
          ((r.map Prod.snd) j).toReal)) =
        ∑ j : Fin M, ∑ m ∈ Finset.univ.erase j, (r (m, j)).toReal := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_mul]
      by_cases hw0 : ((r.map Prod.snd) j).toReal = 0
      · have he0 : (∑ m ∈ Finset.univ.erase j, (r (m, j)).toReal) = 0 := by
          have hle : (∑ m ∈ Finset.univ.erase j, (r (m, j)).toReal) ≤
              ((r.map Prod.snd) j).toReal := by
            rw [PMF.toReal_map_snd_apply]
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              (fun m _ _ => ENNReal.toReal_nonneg)
          exact le_antisymm (hle.trans hw0.le) (Finset.sum_nonneg fun m _ =>
            ENNReal.toReal_nonneg)
        rw [he0]
        simp
      · rw [mul_div_cancel₀ _ hw0]
    have hconc : ConcaveOn ℝ (Set.Icc 0 1) Real.binEntropy :=
      Real.strictConcave_binEntropy.concaveOn
    have hmem : ∀ j ∈ (Finset.univ : Finset (Fin M)),
        ((∑ m ∈ Finset.univ.erase j, (r (m, j)).toReal) /
          ((r.map Prod.snd) j).toReal) ∈ Set.Icc 0 1 := by
      intro j _
      constructor
      · exact div_nonneg (Finset.sum_nonneg fun m _ => ENNReal.toReal_nonneg)
          ENNReal.toReal_nonneg
      · by_cases hw0 : ((r.map Prod.snd) j).toReal = 0
        · rw [hw0]
          simp
        · exact div_le_one_of_le₀ (by
            rw [PMF.toReal_map_snd_apply]
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              (fun m _ _ => ENNReal.toReal_nonneg)) ENNReal.toReal_nonneg
    have hle := hconc.le_map_sum (t := Finset.univ)
      (w := fun j : Fin M => ((r.map Prod.snd) j).toReal)
      (p := fun j : Fin M => (∑ m ∈ Finset.univ.erase j, (r (m, j)).toReal) /
        ((r.map Prod.snd) j).toReal)
      (fun j _ => ENNReal.toReal_nonneg) hsumw hmem
    exact le_trans hle (congrArg Real.binEntropy hwe).le
  have hcond : (∑ j, -(∑ m, (r (m, j)).toReal * Real.log ((r (m, j)).toReal /
      ((r.map Prod.snd) j).toReal)))
      ≤ Real.binEntropy Pe + Pe * Real.log ((M - 1 : ℕ) : ℝ) := by
    calc (∑ j, -(∑ m, (r (m, j)).toReal * Real.log ((r (m, j)).toReal /
          ((r.map Prod.snd) j).toReal)))
        ≤ ∑ j, (((r.map Prod.snd) j).toReal *
            Real.binEntropy ((∑ m ∈ Finset.univ.erase j, (r (m, j)).toReal) /
              ((r.map Prod.snd) j).toReal) +
            (∑ m ∈ Finset.univ.erase j, (r (m, j)).toReal) *
              Real.log ((M - 1 : ℕ) : ℝ)) :=
          Finset.sum_le_sum fun j _ => hper j
      _ = (∑ j, ((r.map Prod.snd) j).toReal *
            Real.binEntropy ((∑ m ∈ Finset.univ.erase j, (r (m, j)).toReal) /
              ((r.map Prod.snd) j).toReal)) +
          Pe * Real.log ((M - 1 : ℕ) : ℝ) := by
          have hsplit : (∑ j, (((r.map Prod.snd) j).toReal *
              Real.binEntropy ((∑ m ∈ Finset.univ.erase j, (r (m, j)).toReal) /
                ((r.map Prod.snd) j).toReal) +
              (∑ m ∈ Finset.univ.erase j, (r (m, j)).toReal) *
                Real.log ((M - 1 : ℕ) : ℝ)))
              = (∑ j, ((r.map Prod.snd) j).toReal *
                  Real.binEntropy ((∑ m ∈ Finset.univ.erase j, (r (m, j)).toReal) /
                    ((r.map Prod.snd) j).toReal)) +
                ∑ j, (∑ m ∈ Finset.univ.erase j, (r (m, j)).toReal) *
                  Real.log ((M - 1 : ℕ) : ℝ) := Finset.sum_add_distrib
          rw [hsplit, ← Finset.sum_mul, ← hPe]
      _ ≤ Real.binEntropy Pe + Pe * Real.log ((M - 1 : ℕ) : ℝ) :=
          add_le_add hJensen le_rfl
  -- Identify the KL sum with `log M` minus the conditional entropy.
  have hS : (∑ t, (r t).toReal * Real.log ((r t).toReal /
      (((r.map Prod.fst) t.1).toReal * ((r.map Prod.snd) t.2).toReal)))
      = Real.log M - (∑ j, -(∑ m, (r (m, j)).toReal * Real.log ((r (m, j)).toReal /
          ((r.map Prod.snd) j).toReal))) := by
    rw [Fintype.sum_prod_type]
    simp only [huni]
    have hperterm : ∀ (m j : Fin M),
        (r (m, j)).toReal * Real.log ((r (m, j)).toReal /
          ((M : ℝ)⁻¹ * ((r.map Prod.snd) j).toReal))
        = (r (m, j)).toReal * Real.log ((r (m, j)).toReal / ((r.map Prod.snd) j).toReal) +
          (r (m, j)).toReal * Real.log M := by
      intro m j
      by_cases hr : (r (m, j)).toReal = 0
      · simp [hr]
      · have hrhat : ((r.map Prod.snd) j).toReal ≠ 0 := by
          have hle : (r (m, j)).toReal ≤ ((r.map Prod.snd) j).toReal := by
            rw [PMF.toReal_map_snd_apply]
            exact Finset.single_le_sum (f := fun a => (r (a, j)).toReal)
              (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ m)
          exact ne_of_gt (lt_of_lt_of_le (lt_of_le_of_ne' ENNReal.toReal_nonneg hr) hle)
        have h1 : (r (m, j)).toReal / ((M : ℝ)⁻¹ * ((r.map Prod.snd) j).toReal)
            = ((r (m, j)).toReal / ((r.map Prod.snd) j).toReal) / (M : ℝ)⁻¹ := by
          rw [mul_comm ((M : ℝ)⁻¹) (((r.map Prod.snd) j).toReal), div_mul_eq_div_div]
        rw [h1, Real.log_div (div_ne_zero hr hrhat) (inv_ne_zero (ne_of_gt hMpos)),
          Real.log_inv]
        ring
    rw [Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => hperterm m j]
    have hsplit : (∑ m, ∑ j, ((r (m, j)).toReal * Real.log ((r (m, j)).toReal /
        ((r.map Prod.snd) j).toReal) + (r (m, j)).toReal * Real.log M))
        = (∑ m, ∑ j, (r (m, j)).toReal * Real.log ((r (m, j)).toReal /
            ((r.map Prod.snd) j).toReal)) +
          (∑ m, ∑ j, (r (m, j)).toReal * Real.log M) := by
      simp_rw [Finset.sum_add_distrib]
    rw [hsplit]
    have hcomm : (∑ m, ∑ j, (r (m, j)).toReal * Real.log ((r (m, j)).toReal /
        ((r.map Prod.snd) j).toReal))
        = ∑ j, ∑ m, (r (m, j)).toReal * Real.log ((r (m, j)).toReal /
          ((r.map Prod.snd) j).toReal) := Finset.sum_comm
    have hsum1 : (∑ j, ∑ m, (r (m, j)).toReal * Real.log ((r (m, j)).toReal /
        ((r.map Prod.snd) j).toReal))
        = -(∑ j, -(∑ m, (r (m, j)).toReal * Real.log ((r (m, j)).toReal /
          ((r.map Prod.snd) j).toReal))) := by
      rw [← Finset.sum_neg_distrib]
      simp only [neg_neg]
    have hsum2 : (∑ m, ∑ j, (r (m, j)).toReal * Real.log M) = Real.log M := by
      simp_rw [← Finset.sum_mul]
      have hsumr : (∑ i, ∑ i_1, (r (i, i_1)).toReal) = 1 :=
        (Fintype.sum_prod_type (fun t : Fin M × Fin M => (r t).toReal)).symm.trans
          (MathlibExt.InformationTheory.GallagerExponent.sum_toReal_eq_one r)
      rw [hsumr, one_mul]
    rw [hcomm, hsum1, hsum2]
    ring
  rw [hS]
  have hPe_nonneg : 0 ≤ Pe := by
    rw [hPe]
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun m _ => ENNReal.toReal_nonneg
  have hlogle : Real.log ((M - 1 : ℕ) : ℝ) ≤ Real.log M := by
    apply Real.log_le_log
    · have h1m : (1 : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ M - 1 by omega)
      linarith
    · rw [Nat.cast_sub (show 1 ≤ M by omega)]
      simp only [Nat.cast_one]
      have hle : ((M : ℝ) - 1) ≤ (M : ℝ) := by linarith
      exact hle
  have hcond' : (∑ j, -(∑ m, (r (m, j)).toReal * Real.log ((r (m, j)).toReal /
      ((r.map Prod.snd) j).toReal)))
      ≤ Real.binEntropy Pe + Pe * Real.log M :=
    le_trans hcond (add_le_add le_rfl (mul_le_mul_of_nonneg_left hlogle hPe_nonneg))
  linarith [hcond']

/-- A crude entropy bound, enough to show the capacity supremum is bounded above. -/
private theorem entropy_bound {γ : Type*} [Fintype γ] (q : PMF γ) :
    shannonEntropy q ≤ Fintype.card γ / Real.log 2 := by
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg one_le_two)
  calc ∑ b, Real.negMulLog (q b).toReal ≤ ∑ _ : γ, (1 : ℝ) :=
         Finset.sum_le_sum fun b _ => (Real.negMulLog_le_one_sub_self ENNReal.toReal_nonneg).trans
           (sub_le_self _ ENNReal.toReal_nonneg)
       _ = _ := by simp

/-- The capacity supremum is bounded above. -/
private theorem information_bddAbove {α β : Type*} [Finite α] [Finite β] (W : α → PMF β) :
    BddAbove (Set.range fun p : PMF α =>
      finiteMutualInformation (p.bind fun a => (W a).map (Prod.mk a))) := by
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  refine ⟨Fintype.card α / Real.log 2 + Fintype.card β / Real.log 2, ?_⟩
  rintro _ ⟨p, rfl⟩
  change finiteMutualInformation (p.bind fun a => (W a).map (Prod.mk a)) ≤ _
  rw [finiteMutualInformation_eq]
  exact (sub_le_self _ (shannonEntropy_nonneg _)).trans
    (add_le_add (entropy_bound _) (entropy_bound _))

/-- The product channel law for one codeword: independent uses of `W`. -/
private noncomputable def prodPMF {α β : Type*} [Fintype β] (W : α → PMF β) {n : ℕ}
    (x : Fin n → α) : PMF (Fin n → β) :=
  PMF.ofFintype (fun y => ∏ i, (W (x i)) (y i)) (by
    have hsum : ∀ a : α, ∑ b, (W a) b = 1 := fun a => by
      rw [← tsum_fintype (L := .unconditional β)]
      exact (W a).tsum_coe
    rw [← Fintype.prod_sum]
    simp only [hsum, Finset.prod_const_one])

private theorem prodPMF_apply_toReal {α β : Type*} [Fintype β] (W : α → PMF β) {n : ℕ}
    (x : Fin n → α) (y : Fin n → β) :
    ((prodPMF W x) y).toReal = ∏ i, ((W (x i)) (y i)).toReal := by
  rw [prodPMF, PMF.ofFintype_apply, ENNReal.toReal_prod]

private theorem prodPMF_succ_apply_toReal {α β : Type*} [Fintype β] (W : α → PMF β)
    {n : ℕ} (a : α) (x : Fin n → α) (b : β) (y : Fin n → β) :
    ((prodPMF W (Fin.cons a x)) (Fin.cons b y)).toReal =
      ((W a) b).toReal * ((prodPMF W x) y).toReal := by
  have h0 : ((W ((Fin.cons a x : Fin (n + 1) → α) (0 : Fin (n + 1))))
      ((Fin.cons b y : Fin (n + 1) → β) (0 : Fin (n + 1)))).toReal =
      ((W a) b).toReal := by rw [Fin.cons_zero, Fin.cons_zero]
  have h1 : (∏ i : Fin n, ((W ((Fin.cons a x : Fin (n + 1) → α) i.succ))
        ((Fin.cons b y : Fin (n + 1) → β) i.succ)).toReal) =
      ∏ i : Fin n, ((W (x i)) (y i)).toReal :=
    Finset.prod_congr rfl fun i _ => by simp [Fin.cons_succ]
  rw [prodPMF_apply_toReal, prodPMF_apply_toReal, Fin.prod_univ_succ, h0, h1]

/-- The joint law of a block input law and the product channel. -/
private noncomputable def jointPMF {α β : Type*} [Fintype β] (W : α → PMF β) (n : ℕ)
    (p : PMF (Fin n → α)) : PMF ((Fin n → α) × (Fin n → β)) :=
  p.bind fun x => (prodPMF W x).map (Prod.mk x)

private theorem jointPMF_apply_toReal {α β : Type*} [Finite α] [Fintype β]
    (W : α → PMF β) (n : ℕ)
    (p : PMF (Fin n → α)) (x : Fin n → α) (y : Fin n → β) :
    ((jointPMF W n p) (x, y)).toReal = (p x).toReal * ((prodPMF W x) y).toReal :=
  bind_joint_apply_toReal p (fun x => prodPMF W x) x y

/-- Splitting a tuple into its head and tail. -/
private def splitEquiv (α : Type*) (n : ℕ) : (Fin (n + 1) → α) ≃ α × (Fin n → α) where
  toFun x := (x 0, Fin.tail x)
  invFun q := Fin.cons q.1 q.2
  left_inv x := Fin.cons_self_tail x
  right_inv q := by
    cases q with
    | mk a x => simp [Fin.cons_zero, Fin.tail_cons]

/-- Mutual information with a one-point output alphabet vanishes. -/
private theorem finiteMutualInformation_eq_zero_of_subsingleton_snd {α β : Type*} [Finite α]
    [Finite β] [Subsingleton β] (p : PMF (α × β)) :
    finiteMutualInformation p = 0 := by
  classical
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  rw [mutualInfo_sum]
  have hsum : (∑ t, (p t).toReal * Real.log ((p t).toReal /
      (((p.map Prod.fst) t.1).toReal * ((p.map Prod.snd) t.2).toReal))) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    obtain ⟨a, b⟩ := t
    have hrx : ((p.map Prod.fst) a).toReal = (p (a, b)).toReal := by
      rw [PMF.toReal_map_fst_apply]
      exact Finset.sum_eq_single b
        (fun b' _ hb' => absurd (Subsingleton.elim b' b) hb')
        (fun hb' => absurd (Finset.mem_univ b) hb')
    have hrhat : ((p.map Prod.snd) b).toReal = 1 := by
      rw [PMF.toReal_map_snd_apply]
      have htot : (∑ a', (p (a', b)).toReal) = ∑ t, (p t).toReal := by
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun a' _ => (Finset.sum_eq_single
          (f := fun y => (p (a', y)).toReal) b
          (fun b' _ hb' => absurd (Subsingleton.elim b' b) hb')
          (fun hb' => absurd (Finset.mem_univ b) hb')).symm
      rw [htot,
        MathlibExt.InformationTheory.GallagerExponent.sum_toReal_eq_one]
    by_cases h0 : (p (a, b)).toReal = 0
    · simp [h0]
    · rw [hrx, hrhat, mul_one, div_self h0, Real.log_one, mul_zero]
  rw [hsum, zero_div]

/-- Tensorization for block laws: the mutual information of an `n`-letter joint law
is at most `n` times the single-letter capacity. -/
private theorem finiteMutualInformation_jointPMF_le {α β : Type*} [Finite α] [Fintype β]
    (W : α → PMF β) (C : ℝ)
    (hC : ∀ q : PMF α, finiteMutualInformation (q.bind fun a => (W a).map (Prod.mk a)) ≤ C) :
    ∀ (n : ℕ) (p : PMF (Fin n → α)),
      finiteMutualInformation (jointPMF W n p) ≤ n * C := by
  classical
  let := Fintype.ofFinite α
  intro n
  induction n with
  | zero =>
    intro p
    have h0 : finiteMutualInformation (jointPMF W 0 p) = 0 := by
      rw [finiteMutualInformation_eq,
        shannonEntropy_eq_zero_of_subsingleton ((jointPMF W 0 p).map Prod.fst),
        shannonEntropy_eq_zero_of_subsingleton ((jointPMF W 0 p).map Prod.snd),
        shannonEntropy_eq_zero_of_subsingleton (jointPMF W 0 p)]
      ring
    rw [h0, Nat.cast_zero, zero_mul]
  | succ n ih =>
    intro p
    classical
    set eα := splitEquiv α n with heα
    set eβ := splitEquiv β n with heβ
    have hsplit : finiteMutualInformation (jointPMF W (n + 1) p) =
        finiteMutualInformation (joint2PMF (p.map eα) W (fun x => prodPMF W x)) := by
      rw [← finiteMutualInformation_map_equiv (jointPMF W (n + 1) p) eα eβ]
      apply finiteMutualInformation_eq_of_toReal
      intro t
      obtain ⟨⟨a, x'⟩, ⟨b, y'⟩⟩ := t
      have h1 : (((jointPMF W (n + 1) p).map (Prod.map ⇑eα ⇑eβ)) ((a, x'), (b, y'))).toReal
          = ((jointPMF W (n + 1) p) (Fin.cons a x', Fin.cons b y')).toReal := by
        have hfun : (Prod.map ⇑eα ⇑eβ :
            (Fin (n + 1) → α) × (Fin (n + 1) → β) →
              (α × (Fin n → α)) × (β × (Fin n → β))) = ⇑(eα.prodCongr eβ) := rfl
        rw [hfun]
        have h2 := map_equiv_apply_toReal (jointPMF W (n + 1) p) (eα.prodCongr eβ)
          (Fin.cons a x', Fin.cons b y')
        have h3 : (eα.prodCongr eβ) (Fin.cons a x', Fin.cons b y') = ((a, x'), (b, y')) := rfl
        rw [h3] at h2
        exact h2
      rw [h1, jointPMF_apply_toReal, joint2PMF_apply_toReal]
      unfold joint2Atom
      rw [show ((p.map eα) (a, x')).toReal = (p (Fin.cons a x')).toReal from
        map_equiv_apply_toReal p eα (Fin.cons a x')]
      rw [prodPMF_succ_apply_toReal]
      ring
    have hI0 : finiteMutualInformation
        (((p.map eα).map Prod.fst).bind fun a => (W a).map (Prod.mk a)) ≤ C :=
      hC _
    have hI1 : finiteMutualInformation
        (((p.map eα).map Prod.snd).bind fun x => (prodPMF W x).map (Prod.mk x)) ≤ n * C :=
      ih _
    have hcast : ((n : ℝ) + 1) * C = (n : ℝ) * C + C := by ring
    rw [hsplit]
    refine le_trans (joint2_mutualInfo_le _ _ _) ?_
    rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring, hcast]
    linarith [hI0, hI1]

/-- The atom of a law pushed forward by a decoder, as a sum over the fibre. -/
private theorem map_prod_id_apply_toReal {α β γ : Type*} [Finite α] [Fintype β] [Finite γ]
    [DecidableEq γ] (p : PMF (α × β)) (g : β → γ) (a : α) (c : γ) :
    ((p.map (Prod.map id g)) (a, c)).toReal =
      ∑ y ∈ Finset.univ.filter (fun y => g y = c), (p (a, y)).toReal := by
  classical
  let := Fintype.ofFinite α
  let := Fintype.ofFinite γ
  have h1 : (p.map (Prod.map id g)) (a, c) =
      ∑ y ∈ Finset.univ.filter (fun y => g y = c), p (a, y) := by
    rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Finset.sum_comm,
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_eq_single a]
    · by_cases hcg : c = g y <;> simp [Prod.mk.injEq, hcg, eq_comm]
    · intro a' _ ha'
      rw [Prod.mk.injEq, ite_eq_right (fun hcon => ha' hcon.1.symm)]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  rw [h1, ENNReal.toReal_sum (fun y _ => PMF.apply_ne_top p (a, y))]

/-- The product law gives a single output word its product probability. -/
private theorem measureReal_singleton_prod {α β : Type*} [Finite α] [Finite β]
    [MeasurableSpace β] [DiscreteMeasurableSpace β] (W : α → PMF β) {n M : ℕ}
    (f : Fin M → Fin n → α) (m : Fin M) (y : Fin n → β) :
    (Measure.pi fun i => (W (f m i)).toMeasure).real {y} =
      ∏ i, ((W (f m i)) (y i)).toReal := by
  classical
  rw [measureReal_def, ← Set.univ_pi_singleton, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]

/-- Tensorization for codebooks: the mutual information of the message with the
channel output is at most `n` times the single-letter capacity. -/
private theorem finiteMutualInformation_message_le {α β : Type*} [Finite α] [Fintype β]
    (W : α → PMF β) (C : ℝ)
    (hC : ∀ q : PMF α, finiteMutualInformation (q.bind fun a => (W a).map (Prod.mk a)) ≤ C) :
    ∀ (n : ℕ) {δ : Type*} [Finite δ] (r : PMF δ) (h : δ → Fin n → α),
      finiteMutualInformation (r.bind fun d => (prodPMF W (h d)).map (Prod.mk d)) ≤ n * C := by
  classical
  let := Fintype.ofFinite α
  intro n
  induction n with
  | zero =>
    intro δ _ r h
    rw [Nat.cast_zero, zero_mul]
    exact (finiteMutualInformation_eq_zero_of_subsingleton_snd
      (r.bind fun d => (prodPMF W (h d)).map (Prod.mk d))).le
  | succ n ih =>
    intro δ _ r h
    classical
    let := Fintype.ofFinite δ
    set eβ := splitEquiv β n with heβ
    set p2 : PMF (δ × (Fin n → α)) := r.map (fun d => (d, Fin.tail (h d))) with hp2
    -- The two-block joint.
    set T := joint2PMF p2 (fun d => W (h d 0)) (fun x => prodPMF W x) with hT
    -- Forget the tail codeword: the message joint is a processing of `T`.
    have hforget : finiteMutualInformation
        (r.bind fun d => (prodPMF W (h d)).map (Prod.mk d)) ≤
        finiteMutualInformation T := by
      have hmap : (r.bind fun d => (prodPMF W (h d)).map (Prod.mk d)) =
          (T.map (Prod.map id ⇑eβ.symm)).map (Prod.map Prod.fst id) := by
        apply pmf_eq_of_toReal_eq
        intro t
        obtain ⟨d, y⟩ := t
        have hT1 : ∀ (d' : δ) (x' : Fin n → α) (y' : Fin (n + 1) → β),
            ((T.map (Prod.map id ⇑eβ.symm)) ((d', x'), y')).toReal =
              (T ((d', x'), (y' 0, Fin.tail y'))).toReal := by
          intro d' x' y'
          have hfun : (Prod.map id ⇑eβ.symm :
              (δ × (Fin n → α)) × (β × (Fin n → β)) →
                (δ × (Fin n → α)) × (Fin (n + 1) → β)) =
              ⇑((Equiv.refl _).prodCongr eβ.symm) := rfl
          rw [hfun]
          have h2 := map_equiv_apply_toReal T ((Equiv.refl _).prodCongr eβ.symm)
            ((d', x'), (y' 0, Fin.tail y'))
          have h3 : ((Equiv.refl _).prodCongr eβ.symm) ((d', x'), (y' 0, Fin.tail y')) =
              ((d', x'), y') :=
            Prod.ext rfl (Fin.cons_self_tail y')
          rw [h3] at h2
          exact h2
        have hfib : ∀ (q : PMF ((δ × (Fin n → α)) × (Fin (n + 1) → β))) (a : δ)
            (z : Fin (n + 1) → β),
            ((q.map (Prod.map Prod.fst id)) (a, z)).toReal =
              ∑ c ∈ Finset.univ.filter (fun c : δ × (Fin n → α) => c.1 = a),
                (q (c, z)).toReal := by
          intro q a z
          have h1 : (q.map (Prod.map Prod.fst id)) (a, z) =
              ∑ c ∈ Finset.univ.filter (fun c : δ × (Fin n → α) => c.1 = a), q (c, z) := by
            rw [PMF.map_apply, tsum_fintype]
            rw [Fintype.sum_prod_type]
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun c _ => ?_
            by_cases hc : c.1 = a
            · rw [Finset.sum_eq_single z]
              · have hcond : (a, z) = Prod.map Prod.fst id (c, z) := Prod.ext hc.symm rfl
                rw [ite_eq_left hcond, ite_eq_left hc]
              · intro z' _ hz'
                rw [Prod.mk.injEq, ite_eq_right (fun hcon => hz' hcon.2.symm)]
              · intro hzcon
                exact absurd (Finset.mem_univ z) hzcon
            · rw [Finset.sum_eq_zero (fun z' _ => by
                rw [Prod.mk.injEq, ite_eq_right (fun hcon => hc hcon.1.symm)])]
              simp [hc]
          rw [h1, ENNReal.toReal_sum (fun c _ => q.apply_ne_top _)]
        have hp2apply : ∀ (d' : δ) (x' : Fin n → α),
            (p2 (d', x')).toReal =
              if Fin.tail (h d') = x' then (r d').toReal else 0 := by
          intro d' x'
          rw [hp2, map_apply_toReal]
          rw [Finset.sum_eq_single d']
          · by_cases hc : Fin.tail (h d') = x'
            · simp [hc]
            · simp [hc]
          · intro d'' _ hd''
            simp [Prod.mk.injEq, hd'']
          · intro hdcon
            exact absurd (Finset.mem_univ d') hdcon
        have h1 : (((T.map (Prod.map id ⇑eβ.symm)).map (Prod.map Prod.fst id)) (d, y)).toReal
            = ∑ x', (T ((d, x'), (y 0, Fin.tail y))).toReal := by
          rw [hfib]
          rw [Finset.sum_filter]
          have hconv : (∑ c : δ × (Fin n → α), if c.1 = d then
              ((T.map (Prod.map id ⇑eβ.symm)) (c, y)).toReal else 0) =
              ∑ x', (T ((d, x'), (y 0, Fin.tail y))).toReal := by
            rw [Fintype.sum_prod_type]
            rw [Finset.sum_eq_single d]
            · refine Finset.sum_congr rfl fun x' _ => ?_
              have hcond : ((d, x').1 = d) := rfl
              rw [ite_eq_left hcond, hT1]
            · intro d' _ hd'
              rw [Finset.sum_eq_zero]
              intro x' _
              simp [hd']
            · intro hdcon
              exact absurd (Finset.mem_univ d) hdcon
          exact hconv
        rw [h1]
        have hsum : (∑ x' : Fin n → α, (T ((d, x'), (y 0, Fin.tail y))).toReal)
            = (r d).toReal * ((prodPMF W (h d)) y).toReal := by
          rw [hT]
          simp_rw [joint2PMF_apply_toReal]
          simp only [joint2Atom]
          simp_rw [hp2apply]
          have hfactor : ∀ x' : Fin n → α,
              (if Fin.tail (h d) = x' then (r d).toReal else 0) *
                ((W (h d 0)) (y 0)).toReal * ((prodPMF W x') (Fin.tail y)).toReal
              = ((W (h d 0)) (y 0)).toReal *
                ((if Fin.tail (h d) = x' then (r d).toReal else 0) *
                  ((prodPMF W x') (Fin.tail y)).toReal) := fun x' => by ring
          rw [Finset.sum_congr rfl fun x' _ => hfactor x', ← Finset.mul_sum]
          have hsingle : (∑ x', (if Fin.tail (h d) = x' then (r d).toReal else 0) *
              ((prodPMF W x') (Fin.tail y)).toReal)
              = (r d).toReal * ((prodPMF W (Fin.tail (h d))) (Fin.tail y)).toReal := by
            rw [Finset.sum_eq_single (Fin.tail (h d))]
            · simp
            · intro x' _ hx'
              rw [ite_eq_right (Ne.symm hx'), zero_mul]
            · intro hxcon
              exact absurd (Finset.mem_univ _) hxcon
          rw [hsingle]
          have hprod : ((prodPMF W (h d)) y).toReal =
              ((W (h d 0)) (y 0)).toReal *
                ((prodPMF W (Fin.tail (h d))) (Fin.tail y)).toReal := by
            conv_lhs => rw [← Fin.cons_self_tail (h d), ← Fin.cons_self_tail y]
            exact prodPMF_succ_apply_toReal W (h d 0) (Fin.tail (h d)) (y 0) (Fin.tail y)
          rw [hprod]
          ring
        rw [hsum]
        exact bind_joint_apply_toReal r (fun d => prodPMF W (h d)) d y
      rw [hmap]
      refine le_trans (finiteMutualInformation_map_fst_le _ _) ?_
      have hfun : (Prod.map ⇑(Equiv.refl (δ × (Fin n → α))) ⇑eβ.symm) =
          Prod.map id ⇑eβ.symm := funext fun _ => rfl
      rw [← hfun, finiteMutualInformation_map_equiv T (Equiv.refl _) eβ.symm]
    have hfst : p2.map Prod.fst = r := by
      rw [hp2, PMF.map_comp]
      have hcomp : Prod.fst ∘ (fun d => (d, Fin.tail (h d))) = (id : δ → δ) :=
        funext fun _ => rfl
      rw [hcomp, PMF.map_id]
    have hI0 : finiteMutualInformation
        (r.bind fun d => (W (h d 0)).map (Prod.mk d)) ≤ C := by
      rw [finiteMutualInformation_bind_map_eq]
      exact hC _
    have hI1 : finiteMutualInformation (jointPMF W n (p2.map Prod.snd)) ≤ (n : ℝ) * C :=
      finiteMutualInformation_jointPMF_le W C hC n _
    rw [hT] at hforget
    refine le_trans hforget (le_trans (joint2_mutualInfo_le _ _ _) ?_)
    rw [hfst]
    change finiteMutualInformation (r.bind fun d => (W (h d 0)).map (Prod.mk d)) +
        finiteMutualInformation (jointPMF W n (p2.map Prod.snd)) ≤ _
    rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring]
    have hcast : ((n : ℝ) + 1) * C = (n : ℝ) * C + C := by ring
    rw [hcast]
    linarith [hI0, hI1]

set_option linter.unusedFintypeInType false in
/-- **Weak converse** (Fano). For a discrete memoryless channel `W` on finite alphabets, every
code with `M ≥ 1` codewords of length `n` and average error probability `Pₑ` satisfies
`(1 - Pₑ) log₂ M ≤ n C(W) + h(Pₑ)`, where `h` is the binary entropy in bits.
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), Theorem 17.3 (`log M ≤ (sup I(X; Y) + h(ε)) / (1 - ε)`) applied to the
`n`-letter channel, with Proposition 19.10 (`sup I(Xⁿ; Yⁿ) = n C`), as in Theorem 19.7. -/
public theorem channelCoding_weak_converse {α β : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [MeasurableSpace β] [DiscreteMeasurableSpace β] (W : α → PMF β) (n M : ℕ)
    (hM : 1 ≤ M) (f : Fin M → Fin n → α) (g : (Fin n → β) → Fin M) :
    let Pe : ℝ := (∑ m, (Measure.pi fun i => (W (f m i)).toMeasure).real {y | g y ≠ m}) / M
    (1 - Pe) * Real.logb 2 M ≤
      n * (⨆ p : PMF α, finiteMutualInformation (p.bind fun a => (W a).map (Prod.mk a))) +
        Real.binEntropy Pe / Real.log 2 := by
  classical
  have hBdd := information_bddAbove W
  have hCnonneg : 0 ≤ ⨆ p : PMF α,
      finiteMutualInformation (p.bind fun a => (W a).map (Prod.mk a)) := by
    have hI0 : 0 ≤ finiteMutualInformation
        ((PMF.pure (Classical.arbitrary α)).bind fun a => (W a).map (Prod.mk a)) := by
      rw [finiteMutualInformation_eq]
      have hle := shannonEntropy_le_add
        ((PMF.pure (Classical.arbitrary α)).bind fun a => (W a).map (Prod.mk a))
      have hnn1 := shannonEntropy_nonneg
        (((PMF.pure (Classical.arbitrary α)).bind fun a => (W a).map (Prod.mk a)).map Prod.fst)
      have hnn2 := shannonEntropy_nonneg
        (((PMF.pure (Classical.arbitrary α)).bind fun a => (W a).map (Prod.mk a)).map Prod.snd)
      linarith
    exact hI0.trans (le_ciSup hBdd _)
  change (1 - ((∑ m, (Measure.pi fun i => (W (f m i)).toMeasure).real {y | g y ≠ m}) / M)) *
      Real.logb 2 M ≤
      n * (⨆ p : PMF α, finiteMutualInformation (p.bind fun a => (W a).map (Prod.mk a))) +
        Real.binEntropy ((∑ m, (Measure.pi fun i => (W (f m i)).toMeasure).real
          {y | g y ≠ m}) / M) / Real.log 2
  set Pe : ℝ := (∑ m, (Measure.pi fun i => (W (f m i)).toMeasure).real {y | g y ≠ m}) / M
    with hPe
  by_cases hM1 : M = 1
  · subst hM1
    have hPe0 : (∑ m : Fin 1, (Measure.pi fun i => (W (f m i)).toMeasure).real
        {y | g y ≠ m}) = 0 := by
      rw [Fin.sum_univ_one]
      have hempty : {y : Fin n → β | g y ≠ (0 : Fin 1)} = ∅ := by
        ext y
        simp [Subsingleton.elim (g y) 0]
      rw [hempty, measureReal_empty]
    rw [hPe, hPe0]
    simp only [Nat.cast_one, Real.binEntropy_zero, zero_div, Real.logb_one,
      mul_zero, sub_zero, add_zero]
    exact mul_nonneg (Nat.cast_nonneg n) hCnonneg
  · have hM2 : 2 ≤ M := by omega
    have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
    have : Nonempty (Fin M) := ⟨⟨0, by omega⟩⟩
    set U : PMF (Fin M) := PMF.uniformFintype (Fin M) with hU
    set R : PMF (Fin M × (Fin n → β)) :=
      U.bind fun m => (prodPMF W (f m)).map (Prod.mk m) with hR
    set Rhat : PMF (Fin M × Fin M) := R.map (Prod.map id g) with hRhat
    have hIR : finiteMutualInformation R ≤ (n : ℝ) *
        (⨆ p : PMF α, finiteMutualInformation (p.bind fun a => (W a).map (Prod.mk a))) := by
      rw [hR]
      exact finiteMutualInformation_message_le W
        (⨆ p : PMF α, finiteMutualInformation (p.bind fun a => (W a).map (Prod.mk a)))
        (fun q => le_ciSup hBdd q) n U f
    have hIhat : finiteMutualInformation Rhat ≤ (n : ℝ) *
        (⨆ p : PMF α, finiteMutualInformation (p.bind fun a => (W a).map (Prod.mk a))) := by
      rw [hRhat]
      exact le_trans (finiteMutualInformation_map_snd_le R g) hIR
    have huni : ∀ m, ((Rhat.map Prod.fst) m).toReal = (M : ℝ)⁻¹ := by
      intro m
      have e1 : ((Rhat.map Prod.fst) m).toReal = ((R.map Prod.fst) m).toReal := by
        congr 1
        rw [hRhat, PMF.map_comp]
        congr 1
      rw [e1, hR, bind_fst_toReal, hU, PMF.uniformFintype_apply, ENNReal.toReal_inv,
        ENNReal.toReal_natCast, Fintype.card_fin]
    have hFano := fano_bound_nats hM2 Rhat huni
    have hS : (∑ t, (Rhat t).toReal * Real.log ((Rhat t).toReal /
        (((Rhat.map Prod.fst) t.1).toReal * ((Rhat.map Prod.snd) t.2).toReal))) =
        finiteMutualInformation Rhat * Real.log 2 := by
      rw [mutualInfo_sum]
      rw [div_mul_cancel₀ _ (Real.log_pos one_lt_two).ne']
    rw [hS] at hFano
    have hdiag : ∀ m : Fin M, (Rhat (m, m)).toReal = (M : ℝ)⁻¹ *
        (Measure.pi fun i => (W (f m i)).toMeasure).real {y | g y = m} := by
      intro m
      have h1 : (Rhat (m, m)).toReal =
          ∑ y ∈ Finset.univ.filter (fun y => g y = m), (R (m, y)).toReal := by
        rw [hRhat]
        exact map_prod_id_apply_toReal R g m m
      rw [h1]
      have h2 : ∀ y : Fin n → β, (R (m, y)).toReal =
          (M : ℝ)⁻¹ * ∏ i, ((W (f m i)) (y i)).toReal := by
        intro y
        rw [hR, bind_joint_apply_toReal, prodPMF_apply_toReal, hU,
          PMF.uniformFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
          Fintype.card_fin]
      rw [Finset.sum_congr rfl fun y _ => h2 y, ← Finset.mul_sum]
      have h3 : (Measure.pi fun i => (W (f m i)).toMeasure).real {y | g y = m} =
          ∑ y ∈ Finset.univ.filter (fun y => g y = m),
            ∏ i, ((W (f m i)) (y i)).toReal := by
        have hset : (↑(Finset.univ.filter (fun y : Fin n → β => g y = m)) :
            Set (Fin n → β)) = {y | g y = m} := by
          ext y
          simp
        rw [← hset, ← sum_measureReal_singleton]
        exact Finset.sum_congr rfl fun y _ => measureReal_singleton_prod W f m y
      rw [h3]
    have hPeF : Pe = ∑ j, ∑ m ∈ Finset.univ.erase j, (Rhat (m, j)).toReal := by
      have hdiag_sum : (∑ j, ∑ m ∈ Finset.univ.erase j, (Rhat (m, j)).toReal)
          = 1 - ∑ m, (Rhat (m, m)).toReal := by
        have hper : ∀ j, (∑ m ∈ Finset.univ.erase j, (Rhat (m, j)).toReal)
            = ((Rhat.map Prod.snd) j).toReal - (Rhat (j, j)).toReal := by
          intro j
          rw [PMF.toReal_map_snd_apply, eq_sub_iff_add_eq, add_comm]
          exact Finset.add_sum_erase Finset.univ (fun m => (Rhat (m, j)).toReal)
            (Finset.mem_univ j)
        rw [Finset.sum_congr rfl fun j _ => hper j, Finset.sum_sub_distrib,
          MathlibExt.InformationTheory.GallagerExponent.sum_toReal_eq_one]
      have hPe_eq : Pe = 1 - ∑ m, (Rhat (m, m)).toReal := by
        rw [hPe]
        have hcomp : ∀ m : Fin M,
            (Measure.pi fun i => (W (f m i)).toMeasure).real {y | g y ≠ m}
              = 1 - (Measure.pi fun i => (W (f m i)).toMeasure).real {y | g y = m} := by
          intro m
          have hset : {y : Fin n → β | g y ≠ m} = {y : Fin n → β | g y = m}ᶜ := by
            ext y
            simp [eq_comm]
          rw [hset]
          exact probReal_compl_eq_one_sub MeasurableSet.of_discrete
        rw [Finset.sum_congr rfl fun m _ => hcomp m, Finset.sum_sub_distrib,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hdiagSum : (∑ m, (Rhat (m, m)).toReal) =
            (∑ m, (Measure.pi fun i => (W (f m i)).toMeasure).real {y | g y = m}) / M := by
          rw [Finset.sum_congr rfl fun m _ => hdiag m, ← Finset.mul_sum, div_eq_mul_inv]
          ring
        rw [hdiagSum]
        field_simp
      rw [hPe_eq, hdiag_sum]
    rw [hPeF]
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
    have hmain : (1 - ∑ j, ∑ m ∈ Finset.univ.erase j, (Rhat (m, j)).toReal) * Real.log M ≤
        (n : ℝ) * (⨆ p : PMF α,
          finiteMutualInformation (p.bind fun a => (W a).map (Prod.mk a))) * Real.log 2 +
          Real.binEntropy (∑ j, ∑ m ∈ Finset.univ.erase j, (Rhat (m, j)).toReal) :=
      le_trans hFano (add_le_add
        (mul_le_mul_of_nonneg_right hIhat hlog2pos.le) le_rfl)
    rw [Real.logb, ← mul_div_assoc, div_le_iff₀ hlog2pos, add_mul,
      div_mul_cancel₀ _ hlog2pos.ne']
    linarith [hmain]

end MathlibExt.InformationTheory.ChannelCodingWanted
