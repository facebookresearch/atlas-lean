/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sequence.HiddenMarkovLaw
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
import MathlibExt.Probability.ProbabilityMassFunction.Marginal

/-!
# Joint law of a normalized hidden Markov model as an actual PMF

`HiddenMarkovLaw.jointProb` gives the joint law on hidden paths and
observation strings as a real number. This file builds the same law as
an actual probability object and identifies their masses.

`jointPMF` is a `PMF` on paths × observations built by `PMF.bind`:
sample a hidden path from `pathPMF` (initial state from `initPMF`, then
one `transPMF` step per time), then sample observations from `obsPMF`
(one `emitPMF` per time, independent given the path). The leaf PMFs use
`PMF.ofFintype (ENNReal.ofReal ∘ weights)` with total-mass side
conditions proved from the `Normalized` fields, so the objects have
total mass one by construction; no positivity is assumed anywhere
(zeros are allowed, as in `Normalized`).

Main identifications:

* `jointPMF_apply_toReal`: the real value of the joint PMF mass is
  `jointProb`.
* `jointProb_factor`: `jointProb` factors as hidden-path prior weight
  (`pathWeight`) times observation weight (`obsWeight`).
* `obsMarginal_apply_toReal` / `pathMarginal_apply_ofReal`: the two
  marginals of `jointPMF` are the likelihood and the path prior.
-/

@[expose] public section

namespace Cslib.MachineLearning.Sequence.HiddenMarkovMeasure

open Cslib.MachineLearning.Sequence.HiddenMarkov
open Cslib.MachineLearning.Sequence.HiddenMarkovLaw

variable {S O : Type*} [Fintype S] [Fintype O]

/-! ## Proof helpers for the finite real-valued total

Small `Fin.snoc` and `extend` facts supporting the `snoc` recurrence of
the joint law and, through it, the factorization below. -/

/-- `Fin.snoc` applied at a `castSucc` index. -/
private theorem snoc_castSucc_apply {α : Type*} (t : ℕ) (p : Fin (t + 1) → α)
    (a : α) (i : Fin (t + 1)) :
    (Fin.snoc (α := fun _ => α) p a) i.castSucc = p i := by
  simp

/-- `Fin.snoc` applied at the last index. -/
private theorem snoc_last_apply {α : Type*} (t : ℕ) (p : Fin (t + 1) → α)
    (a : α) :
    (Fin.snoc (α := fun _ => α) p a) (Fin.last (t + 1)) = a := by
  simp

/-- `castSucc` of `0` is `0`. -/
private theorem castSucc_zero_eq (t : ℕ) :
    ((0 : Fin (t + 1)).castSucc) = 0 := by
  simp

/-- `extend` evaluates to the string on indices `≤ t`. -/
theorem extend_apply_le (t : ℕ) (v : Fin (t + 1) → O) (i : ℕ)
    (hi : i ≤ t) :
    extend t v i = v ⟨i, by omega⟩ := by
  simp only [extend]
  rw [dite_eq_left hi]

/-- Multi-time `snoc` recurrence for the joint law: extending path and
string by one step multiplies the joint weight by the transition and
emission weights of the new step. -/
theorem jointProb_snoc (h : HMM S O ℝ) (t : ℕ)
    (z : Fin (t + 1) → S) (x : Fin (t + 1) → O) (s : S) (o : O) :
    jointProb S O h (t + 1) (Fin.snoc z s, Fin.snoc x o) =
      jointProb S O h t (z, x) * h.trans (z (Fin.last t)) s *
        h.emit s o := by
  have hagree : ∀ i, i ≤ t →
      extend (t + 1) (Fin.snoc x o) i = extend t x i := by
    intro i hi
    rw [extend_apply_le (t + 1) (Fin.snoc x o) i (by omega),
      extend_apply_le t x i hi]
    have hcast : ∀ (j : ℕ) (h1 : j < t + 1 + 1) (h2 : j < t + 1),
        (⟨j, h1⟩ : Fin (t + 1 + 1)) =
          ((⟨j, h2⟩ : Fin (t + 1)).castSucc) := fun j h1 h2 => rfl
    rw [hcast i _ (by omega)]
    exact snoc_castSucc_apply t x o ⟨i, by omega⟩
  have hlast : extend (t + 1) (Fin.snoc x o) (t + 1) = o := by
    rw [extend_apply_le (t + 1) (Fin.snoc x o) (t + 1) (by omega)]
    have hlast' : ∀ (h1 : t + 1 < t + 1 + 1),
        (⟨t + 1, h1⟩ : Fin (t + 1 + 1)) = Fin.last (t + 1) :=
      fun h1 => rfl
    rw [hlast']
    exact snoc_last_apply t x o
  have hcongr : pathProb h (extend (t + 1) (Fin.snoc x o)) t z =
      pathProb h (extend t x) t z :=
    HiddenMarkovLaw.pathProb_congr S O h _ _ t hagree z
  simp only [jointProb]
  rw [pathProb_snoc, hlast, hcongr]

/-! ## Actual probability objects

Leaf kernel PMFs. Each `PMF.ofFintype` side condition is proved
directly from `hN`; `PMF.bind`/`PMF.map` preserve total mass one
by construction, so `pathPMF`, `obsPMF` and `jointPMF` are total
probability objects definitionally. -/

/-- Initial-state PMF of a normalized HMM. -/
def initPMF (h : HMM S O ℝ) (hN : Normalized h) : PMF S :=
  PMF.ofFintype (fun s => ENNReal.ofReal (h.init s)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (fun s _ => hN.init_nonneg s), hN.init_sum, ENNReal.ofReal_one])

/-- Transition kernel PMF from state `s`. -/
def transPMF (h : HMM S O ℝ) (hN : Normalized h) (s : S) : PMF S :=
  PMF.ofFintype (fun s' => ENNReal.ofReal (h.trans s s')) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (fun s' _ => hN.trans_nonneg s s'), hN.trans_sum s,
      ENNReal.ofReal_one])

/-- Emission kernel PMF from state `s`. -/
def emitPMF (h : HMM S O ℝ) (hN : Normalized h) (s : S) : PMF O :=
  PMF.ofFintype (fun o => ENNReal.ofReal (h.emit s o)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (fun o _ => hN.emit_nonneg s o), hN.emit_sum s,
      ENNReal.ofReal_one])

/-- Hidden-path prior PMF at horizon `t`: initial state, then one
transition step per time. -/
noncomputable def pathPMF (h : HMM S O ℝ) (hN : Normalized h) :
    (t : ℕ) → PMF (Fin (t + 1) → S)
  | 0 => PMF.map (fun s _ => s) (initPMF h hN)
  | t + 1 => PMF.bind (pathPMF h hN t)
      (fun z => PMF.map (Fin.snoc z)
        (transPMF h hN (z (Fin.last t))))

/-- Observation kernel PMF given hidden path `z`: emissions are
independent across time given the path. -/
noncomputable def obsPMF (h : HMM S O ℝ) (hN : Normalized h) :
    (t : ℕ) → (Fin (t + 1) → S) → PMF (Fin (t + 1) → O)
  | 0, z => PMF.map (fun o _ => o) (emitPMF h hN (z 0))
  | t + 1, z => PMF.bind (obsPMF h hN t (Fin.init z))
      (fun x => PMF.map (Fin.snoc x)
        (emitPMF h hN (z (Fin.last (t + 1)))))

/-- The joint PMF on paths and observations at horizon `t`: sample
a hidden path from `pathPMF`, then observations from `obsPMF`. -/
noncomputable def jointPMF (h : HMM S O ℝ) (hN : Normalized h) (t : ℕ) :
    PMF ((Fin (t + 1) → S) × (Fin (t + 1) → O)) :=
  PMF.bind (pathPMF h hN t)
    (fun z => PMF.map (Prod.mk z) (obsPMF h hN t z))

/-! ## Factorization weights (real-valued)

`jointProb` factors as hidden-path
prior mass times observation-kernel mass, with zero cells allowed
(no positivity hypothesis anywhere). -/

/-- Prior weight of hidden path `z`: initial mass times the product
of transition masses along the path. -/
def pathWeight (h : HMM S O ℝ) (t : ℕ) (z : Fin (t + 1) → S) : ℝ :=
  h.init (z 0) * ∏ i : Fin t, h.trans (z i.castSucc) (z i.succ)

/-- Observation weight of string `x` given path `z`: the product of
emission masses along the path. -/
def obsWeight (h : HMM S O ℝ) (t : ℕ) (z : Fin (t + 1) → S)
    (x : Fin (t + 1) → O) : ℝ :=
  ∏ i : Fin (t + 1), h.emit (z i) (x i)

/-! ## Proof helpers for mass identification (Block B)

Weight recurrences, nonnegativity, and PMF unfolding helpers. -/

/-- `pathWeight` recurrence under `snoc`. -/
private theorem pathWeight_snoc (h : HMM S O ℝ) (t : ℕ)
    (z : Fin (t + 1) → S) (s : S) :
    pathWeight h (t + 1) (Fin.snoc z s) =
      pathWeight h t z * h.trans (z (Fin.last t)) s := by
  have hs : ∀ i : Fin t, (i.castSucc).succ = (i.succ).castSucc :=
    fun i => rfl
  have hl : (Fin.last t).succ = Fin.last (t + 1) := rfl
  have h0 : (Fin.snoc (α := fun _ => S) z s) 0 = z 0 := by
    have h := snoc_castSucc_apply t z s 0
    simpa [castSucc_zero_eq t] using h
  simp only [pathWeight]
  rw [Fin.prod_univ_castSucc]
  simp only [snoc_castSucc_apply, snoc_last_apply, h0, hs, hl]
  ring

/-- `obsWeight` recurrence under `snoc`. -/
private theorem obsWeight_snoc (h : HMM S O ℝ) (t : ℕ)
    (z : Fin (t + 1) → S) (x : Fin (t + 1) → O) (s : S) (o : O) :
    obsWeight h (t + 1) (Fin.snoc z s) (Fin.snoc x o) =
      obsWeight h t z x * h.emit s o := by
  simp only [obsWeight]
  rw [Fin.prod_univ_castSucc]
  simp only [snoc_castSucc_apply, snoc_last_apply]
  try ring

/-- `pathWeight` is nonnegative. -/
private theorem pathWeight_nonneg (h : HMM S O ℝ) (hN : Normalized h) (t : ℕ)
    (z : Fin (t + 1) → S) : 0 ≤ pathWeight h t z := by
  simp only [pathWeight]
  exact mul_nonneg (hN.init_nonneg _)
    (Finset.prod_nonneg (fun i _ => hN.trans_nonneg _ _))

/-- `obsWeight` is nonnegative. -/
private theorem obsWeight_nonneg (h : HMM S O ℝ) (hN : Normalized h) (t : ℕ)
    (z : Fin (t + 1) → S) (x : Fin (t + 1) → O) :
    0 ≤ obsWeight h t z x := by
  simp only [obsWeight]
  exact Finset.prod_nonneg (fun i _ => hN.emit_nonneg _ _)

private theorem map_apply_single {α β : Type*} (q : PMF α) (f : α → β)
    (a₀ : α) (b : β) (hf : ∀ a, f a = b → a = a₀)
    (hb : f a₀ = b) :
    (PMF.map f q) b = q a₀ := by
  classical
  have hvan : ∀ a : α, a ≠ a₀ →
      q a * (if b = f a then (1 : ENNReal) else 0) = 0 := by
    intro a ha
    have hne : ¬(b = f a) := fun heq => ha (hf a heq.symm)
    rw [ite_eq_right hne, mul_zero]
  simp only [PMF.map, PMF.bind_apply, Function.comp_apply, PMF.pure_apply]
  rw [tsum_eq_single a₀ hvan, ite_eq_left hb.symm, mul_one]

private theorem map_apply_eq_zero {α β : Type*} (q : PMF α) (f : α → β)
    (b : β) (hf : ∀ a, f a ≠ b) :
    (PMF.map f q) b = 0 := by
  classical
  have hvan : ∀ a : α,
      q a * (if b = f a then (1 : ENNReal) else 0) = 0 := by
    intro a
    rw [ite_eq_right (Ne.symm (hf a)), mul_zero]
  simp only [PMF.map, PMF.bind_apply, Function.comp_apply, PMF.pure_apply]
  simp [hvan]

private theorem jointPMF_bind_apply (h : HMM S O ℝ) (hN : Normalized h)
    (t : ℕ) (z : Fin (t + 1) → S) (x : Fin (t + 1) → O) :
    (jointPMF h hN t) (z, x) =
      (pathPMF h hN t) z * (obsPMF h hN t z) x := by
  have h1 : ∀ z' : Fin (t + 1) → S, z' ≠ z →
      (pathPMF h hN t) z' *
        (∑' x' : Fin (t + 1) → O, (obsPMF h hN t z') x' *
          PMF.pure (z', x') (z, x)) = 0 := by
    intro z' hz'
    have hvan : ∀ x' : Fin (t + 1) → O,
        (obsPMF h hN t z') x' * PMF.pure (z', x') (z, x) = 0 := by
      intro x'
      rw [PMF.pure_apply_of_ne _ _
        (fun heq => hz' (congrArg Prod.fst heq).symm), mul_zero]
    simp only [hvan, tsum_zero, mul_zero]
  have h2 : ∀ x' : Fin (t + 1) → O, x' ≠ x →
      (obsPMF h hN t z) x' * PMF.pure (z, x') (z, x) = 0 := by
    intro x' hx'
    rw [PMF.pure_apply_of_ne _ _
      (fun heq => hx' (congrArg Prod.snd heq).symm), mul_zero]
  simp only [jointPMF, PMF.map, PMF.bind_apply, Function.comp_apply]
  rw [tsum_eq_single z h1, tsum_eq_single x h2, PMF.pure_apply_self, mul_one]

/-! ## Mass-identification theorems -/

theorem pathPMF_apply (h : HMM S O ℝ) (hN : Normalized h) (t : ℕ)
    (z : Fin (t + 1) → S) :
    (pathPMF h hN t) z = ENNReal.ofReal (pathWeight h t z) := by
  induction t with
  | zero =>
      haveI : Unique (Fin (0 + 1)) := Fin.instUnique
      have hz : z = fun _ => z 0 := by
        funext i
        have hi : i = 0 :=
          (Unique.eq_default i).trans (Unique.eq_default 0).symm
        rw [hi]
      have hof : (initPMF h hN) (z 0) =
          ENNReal.ofReal (h.init (z 0)) := rfl
      have hpw : pathWeight h 0 z = h.init (z 0) := by simp [pathWeight]
      simp only [pathPMF]
      rw [map_apply_single _ (fun s _ => s) (z 0) z
        (fun s' h => congrFun h 0) hz.symm, hof, hpw]
  | succ t IH =>
      have hzz : z = Fin.snoc (Fin.init z) (z (Fin.last (t + 1))) := by
        simp
      have step : ∀ (z' : Fin (t + 1) → S) (s : S),
          (pathPMF h hN (t + 1)) (Fin.snoc (α := fun _ => S) z' s) =
            ENNReal.ofReal
              (pathWeight h (t + 1) (Fin.snoc (α := fun _ => S) z' s)) := by
        intro z' s
        simp only [pathPMF, PMF.bind_apply]
        have h_outer : ∀ z'' : Fin (t + 1) → S, z'' ≠ z' →
            (pathPMF h hN t) z'' *
              (PMF.map (Fin.snoc (α := fun _ => S) z'')
                (transPMF h hN (z'' (Fin.last t)))) (Fin.snoc (α := fun _ => S) z' s) =
              0 := by
          intro z'' hz''
          have hmap0 := map_apply_eq_zero
            (transPMF h hN (z'' (Fin.last t))) (Fin.snoc (α := fun _ => S) z'')
            (Fin.snoc (α := fun _ => S) z' s)
            (fun a heq => hz'' (by
              simpa [Fin.init_snoc] using congrArg Fin.init heq))
          rw [hmap0, mul_zero]
        rw [tsum_eq_single z' h_outer]
        rw [map_apply_single _ (Fin.snoc (α := fun _ => S) z') s (Fin.snoc (α := fun _ => S) z' s)
          (fun a heq => by
            simpa [snoc_last_apply] using
              congrArg (fun w => w (Fin.last (t + 1))) heq) rfl]
        rw [IH,
          show (transPMF h hN (z' (Fin.last t))) s =
              ENNReal.ofReal (h.trans (z' (Fin.last t)) s) from rfl,
          ← ENNReal.ofReal_mul (pathWeight_nonneg h hN t z'),
          ← pathWeight_snoc]
      rw [hzz]
      exact step _ _

theorem obsPMF_apply (h : HMM S O ℝ) (hN : Normalized h) (t : ℕ)
    (z : Fin (t + 1) → S) (x : Fin (t + 1) → O) :
    (obsPMF h hN t z) x = ENNReal.ofReal (obsWeight h t z x) := by
  induction t with
  | zero =>
      haveI : Unique (Fin (0 + 1)) := Fin.instUnique
      have hx : x = fun _ => x 0 := by
        funext i
        have hi : i = 0 :=
          (Unique.eq_default i).trans (Unique.eq_default 0).symm
        rw [hi]
      have hof : (emitPMF h hN (z 0)) (x 0) =
          ENNReal.ofReal (h.emit (z 0) (x 0)) := rfl
      have how : obsWeight h 0 z x = h.emit (z 0) (x 0) := by
        simp only [obsWeight]
        rw [Fin.prod_univ_succ]
        simp
      simp only [obsPMF]
      rw [map_apply_single _ (fun o _ => o) (x 0) x
        (fun o' h => congrFun h 0) hx.symm, hof, how]
  | succ t IH =>
      have hzz : z = Fin.snoc (Fin.init z) (z (Fin.last (t + 1))) := by
        simp
      have hxx : x = Fin.snoc (Fin.init x) (x (Fin.last (t + 1))) := by
        simp
      have step : ∀ (z' : Fin (t + 1) → S) (x' : Fin (t + 1) → O)
          (s : S) (o : O),
          (obsPMF h hN (t + 1) (Fin.snoc z' s)) (Fin.snoc (α := fun _ => O) x' o) =
            ENNReal.ofReal
              (obsWeight h (t + 1) (Fin.snoc z' s)
                (Fin.snoc (α := fun _ => O) x' o)) := by
        intro z' x' s o
        simp only [obsPMF, PMF.bind_apply, Fin.init_snoc,
          snoc_last_apply]
        have h_outer : ∀ x'' : Fin (t + 1) → O, x'' ≠ x' →
            (obsPMF h hN t z') x'' *
              (PMF.map (Fin.snoc (α := fun _ => O) x'') (emitPMF h hN s))
                (Fin.snoc (α := fun _ => O) x' o) = 0 := by
          intro x'' hx''
          have hmap0 := map_apply_eq_zero (emitPMF h hN s)
            (Fin.snoc (α := fun _ => O) x'') (Fin.snoc (α := fun _ => O) x' o)
            (fun a heq => hx'' (by
              simpa [Fin.init_snoc] using congrArg Fin.init heq))
          rw [hmap0, mul_zero]
        rw [tsum_eq_single x' h_outer]
        rw [map_apply_single _ (Fin.snoc (α := fun _ => O) x') o (Fin.snoc (α := fun _ => O) x' o)
          (fun a heq => by
            simpa [snoc_last_apply] using
              congrArg (fun w => w (Fin.last (t + 1))) heq) rfl]
        rw [IH, show (emitPMF h hN s) o =
            ENNReal.ofReal (h.emit s o) from rfl,
          ← ENNReal.ofReal_mul (obsWeight_nonneg h hN t z' x'),
          ← obsWeight_snoc]
      rw [hzz, hxx]
      exact step _ _ _ _

/-- Prior/emission factorization of the joint law. No positivity
hypothesis: zero transition or emission cells are allowed and make
both sides zero through the corresponding factor. -/
theorem jointProb_factor (h : HMM S O ℝ) (t : ℕ)
    (z : Fin (t + 1) → S) (x : Fin (t + 1) → O) :
    jointProb S O h t (z, x) = pathWeight h t z * obsWeight h t z x := by
  have hemit : (∏ i : Fin (t + 1), h.emit (z i) (extend t x i)) =
      ∏ i : Fin (t + 1), h.emit (z i) (x i) :=
    Finset.prod_congr rfl fun i _ => by
      rw [extend_apply_le t x (i : ℕ) (Nat.le_of_lt_succ i.isLt)]
  rw [show jointProb S O h t (z, x) = pathProb h (extend t x) t z from rfl,
    HiddenMarkov.pathProb_eq_prod, hemit, pathWeight, obsWeight, mul_assoc]

theorem jointPMF_apply (h : HMM S O ℝ) (hN : Normalized h) (t : ℕ)
    (z : Fin (t + 1) → S) (x : Fin (t + 1) → O) :
    (jointPMF h hN t) (z, x) = ENNReal.ofReal (jointProb S O h t (z, x)) := by
  rw [jointPMF_bind_apply, pathPMF_apply, obsPMF_apply,
    ← ENNReal.ofReal_mul (pathWeight_nonneg h hN t z), jointProb_factor]

theorem jointPMF_apply_toReal (h : HMM S O ℝ) (hN : Normalized h)
    (t : ℕ) (z : Fin (t + 1) → S) (x : Fin (t + 1) → O) :
    ((jointPMF h hN t) (z, x)).toReal = jointProb S O h t (z, x) := by
  have hnn : 0 ≤ jointProb S O h t (z, x) := by
    rw [jointProb_factor]
    exact mul_nonneg (pathWeight_nonneg h hN t z)
      (obsWeight_nonneg h hN t z x)
  rw [jointPMF_apply, ENNReal.toReal_ofReal hnn]

theorem jointProb_nonneg (h : HMM S O ℝ) (hN : Normalized h) (t : ℕ)
    (zx : (Fin (t + 1) → S) × (Fin (t + 1) → O)) :
    0 ≤ jointProb S O h t zx := by
  obtain ⟨z, x⟩ := zx
  rw [jointProb_factor]
  exact mul_nonneg (pathWeight_nonneg h hN t z)
    (obsWeight_nonneg h hN t z x)


/-- The observation marginal (`Prod.snd`) of the joint PMF has mass
`likelihood` at each observation string, in `ENNReal`. The
`Normalized` hypothesis is needed here (unlike in
`likelihood_eq_sum_jointProb`) because `jointPMF` itself is only
defined for normalized parameters. -/
theorem obsMarginal_apply (h : HMM S O ℝ) (hN : Normalized h)
    (t : ℕ) (x : Fin (t + 1) → O) :
    (PMF.map Prod.snd (jointPMF h hN t)) x =
      ENNReal.ofReal (likelihood h (extend t x) t) := by
  rw [PMF.map_snd_apply]
  have hcell : ∀ z : Fin (t + 1) → S,
      (jointPMF h hN t) (z, x) =
        ENNReal.ofReal (jointProb S O h t (z, x)) :=
    fun z => jointPMF_apply h hN t z x
  rw [Finset.sum_congr rfl (fun z _ => hcell z),
    ← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (fun z _ => jointProb_nonneg h hN t (z, x)),
    HiddenMarkovLaw.likelihood_eq_sum_jointProb]

/-- The observation marginal mass equals `likelihood`, as a real
number. -/
theorem obsMarginal_apply_toReal (h : HMM S O ℝ) (hN : Normalized h)
    (t : ℕ) (x : Fin (t + 1) → O) :
    ((PMF.map Prod.snd (jointPMF h hN t)) x).toReal =
      likelihood h (extend t x) t := by
  have hnn : 0 ≤ likelihood h (extend t x) t := by
    rw [HiddenMarkovLaw.likelihood_eq_sum_jointProb]
    exact Finset.sum_nonneg (fun z _ => jointProb_nonneg h hN t (z, x))
  rw [obsMarginal_apply, ENNReal.toReal_ofReal hnn]

/-- The hidden-path marginal (`Prod.fst`) of the joint PMF recovers
the path prior PMF exactly (observations sum out by construction). -/
theorem pathMarginal_apply (h : HMM S O ℝ) (hN : Normalized h)
    (t : ℕ) (z : Fin (t + 1) → S) :
    (PMF.map Prod.fst (jointPMF h hN t)) z = (pathPMF h hN t) z := by
  have hobs : ∀ z' : Fin (t + 1) → S,
      (∑ x' : Fin (t + 1) → O, (obsPMF h hN t z') x') = 1 := by
    intro z'
    have h := PMF.tsum_coe (obsPMF h hN t z')
    rwa [tsum_fintype] at h
  have hcell : ∀ (z' : Fin (t + 1) → S) (x' : Fin (t + 1) → O),
      (jointPMF h hN t) (z', x') =
        (pathPMF h hN t) z' * (obsPMF h hN t z') x' :=
    fun z' x' => jointPMF_bind_apply h hN t z' x'
  rw [PMF.map_fst_apply]
  simp_rw [hcell]
  rw [← Finset.mul_sum, hobs, mul_one]

/-- The hidden-path marginal mass equals `pathWeight`, in `ENNReal`. -/
theorem pathMarginal_apply_ofReal (h : HMM S O ℝ) (hN : Normalized h)
    (t : ℕ) (z : Fin (t + 1) → S) :
    (PMF.map Prod.fst (jointPMF h hN t)) z =
      ENNReal.ofReal (pathWeight h t z) := by
  rw [pathMarginal_apply, pathPMF_apply]

/-- The joint PMF is normalized (definitional from `PMF.bind`, but
stated for the test plan). -/
theorem jointPMF_total (h : HMM S O ℝ) (hN : Normalized h) (t : ℕ) :
    ∑' zx : (Fin (t + 1) → S) × (Fin (t + 1) → O),
      (jointPMF h hN t) zx = 1 := by
  exact PMF.tsum_coe _

end Cslib.MachineLearning.Sequence.HiddenMarkovMeasure
