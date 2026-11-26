/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Configuration
public import CSLibExt.Crypto.Framework.Asymptotic

/-!
# Exact fair-bit sampling with a running-time tail

A finite table chooses a CSLib multi-tape action from the current state, symbols under the heads,
and one fresh fair bit. An action is one machine step, not an uncharged operation on whole words.
The output tape of the very same run determines its law. We account for two steps at a time:
observing a halt one step later does not change its output, and rounds a deadline up by at most
one step. A bound of $p(n)$ checkpoints is a bound of $2p(n)$ native transitions.

This is the sequential fresh-coin model, not a random-access random tape. The efficiency and
almost-sure termination conventions follow Boneh and Shoup, *A Graduate Course in Applied
Cryptography*, v0.4, §2.4.2, Definitions 2.8–2.9 and the footnote on p. 30.
-/

@[expose] public section

namespace Cslib.Crypto.Framework

open _root_.Turing
open scoped ENNReal
local notation "Bits" => List Bool

/-- **A fair-bit sampler.** A fixed finite control and a fixed number of binary work tapes,
with the ordinary bounded-head read-only input and write-only output. The finite transition
table selects a single local action given the state, symbols under the heads and a fresh fair
bit. It may ignore that bit. There are no transition probabilities supplied by the caller. -/
structure FairSampler where
  tapes : ℕ
  State : Type
  [finiteState : Fintype State]
  start : State
  table : State → Option Bool → (Fin tapes → Option Bool) → Bool → Action tapes Bool State

namespace FairSampler

variable (M : FairSampler) {x : Bits}
local notation "Cfgₓ" => Cfg M.tapes Bool M.State x

/-- **One charged transition.** A live sampler applies its selected local machine action. A
halted configuration is absorbing, including its output tape. -/
def step (c : Cfgₓ) (b : Bool) : Cfgₓ :=
  match c.state with
  | none => c
  | some q => (M.table q c.inputSymbol c.workTapeSymbols b).apply c

@[simp] theorem step_of_halted (c : Cfgₓ) (h : c.Halted) (b : Bool) : M.step c b = c := by
  simp [step, h]

abbrev two (c : Cfgₓ) (a b : Bool) : Cfgₓ := M.step (M.step c a) b

noncomputable abbrev avg (f : Bool → Bool → ℝ≥0∞) :=
  (4 : ℝ≥0∞)⁻¹ * (f false false + f false true + f true false + f true true)

@[simp] theorem avg_const (r : ℝ≥0∞) : avg (fun _ _ => r) = r := by
  change 4⁻¹ * (r + r + r + r) = r
  rw [show r + r + r + r = 4 * r by ring, ← mul_assoc,
    ENNReal.inv_mul_cancel (by norm_num) (by simp), one_mul]

/-- **First-halt probability.** At checkpoint zero it is the indicator of already being
halted with output $y$. At a later checkpoint a previously halted configuration contributes
zero; a live one averages the preceding-checkpoint probabilities over two fresh fair steps. -/
noncomputable def hit (y : Bits) (n : ℕ) (c : Cfgₓ) : ℝ≥0∞ :=
  match n with
  | 0 => if c.Halted ∧ c.output = y then 1 else 0
  | n + 1 => if c.Halted then 0 else avg fun a b => hit y n (M.two c a b)

/-- **Running-time tail.** The probability that the sampler started in the given configuration
has not halted after $2n$ native machine steps. -/
noncomputable def live (n : ℕ) (c : Cfgₓ) : ℝ≥0∞ :=
  match n with
  | 0 => if c.Halted then 0 else 1
  | n + 1 => if c.Halted then 0 else avg fun a b => live n (M.two c a b)

/-- A history through $n$ two-step checkpoints, in chronological order. -/
def History : ℕ → Type
  | 0 => Unit
  | n + 1 => (Bool × Bool) × History n

instance : (n : ℕ) → Fintype (History n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => @instFintypeProd _ _ inferInstance (instFintypeHistory n)

def first (y : Bits) : (n : ℕ) → Cfgₓ → History n → Prop
  | 0, c, _ => c.Halted ∧ c.output = y
  | t+1, c, (b, w) => ¬ c.Halted ∧ first y t (M.two c b.1 b.2) w

def run : (n : ℕ) → Cfgₓ → History n → Cfgₓ
  | 0, c, _ => c
  | n+1, c, (b, w) => run n (M.two c b.1 b.2) w

theorem run_of_halted (n : ℕ) (c : Cfgₓ) (h : c.Halted) (w : History n) : M.run n c w = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨⟨a,b⟩, w⟩ := w
    simpa only [run, two, M.step_of_halted c h] using ih w

open scoped Classical in
/-- The first-halt probability is $4^{-n}$ times the number of length-$n$ pair histories
which first observe a halt with the specified output at that checkpoint. -/
theorem hit_eq_cylinders (y : Bits) (n : ℕ) (c : Cfgₓ) :
    M.hit y n c = (4 : ℝ≥0∞)⁻¹ ^ n * ∑ w : History n, (if M.first y n c w then 1 else 0) := by
  classical
  induction n generalizing c with
  | zero =>
    change (if c.Halted ∧ c.output = y then 1 else 0) = _ * ∑ _ : Unit, _
    by_cases h : c.Halted ∧ c.output = y <;> simp [first, h]
  | succ n ih =>
    change M.hit y (n+1) c = _ * ∑ p : (Bool × Bool) × History n, _
    by_cases h : c.Halted
    · simp [hit, first, h]
    · simp only [hit, ite_false, avg, ih, Fintype.sum_prod_type, Fintype.sum_bool, first, h,
        not_false_eq_true, true_and, pow_succ']
      ring

open scoped Classical in
/-- The time tail is $4^{-n}$ times the number of length-$n$ pair histories whose final
configuration is still live. -/
theorem live_eq_cylinders (n : ℕ) (c : Cfgₓ) :
    M.live n c = (4 : ℝ≥0∞)⁻¹ ^ n * ∑ w : History n, (if (M.run n c w).Halted then 0 else 1) := by
  classical
  induction n generalizing c with
  | zero =>
    change (if c.Halted then 0 else 1) = _ * ∑ _ : Unit, _
    by_cases h : c.state = none <;> simp [run, Cfg.Halted, h]
  | succ n ih =>
    by_cases h : c.Halted
    · rw [live, ite_eq_left h]
      simp only [M.run_of_halted _ c h]
      simp [Cfg.Halted, show c.state = none from h]
    · change M.live (n+1) c = _ * ∑ p : (Bool × Bool) × History n, _
      simp only [live, h, ite_false, avg, ih, Fintype.sum_prod_type, Fintype.sum_bool, run,
        pow_succ', mul_add, mul_assoc]
      ac_rfl

private theorem avg_sum {ι : Type*} (s : Finset ι) (f : ι → Bool → Bool → ℝ≥0∞) :
    ∑ i ∈ s, avg (f i) = avg (fun a b => ∑ i ∈ s, f i a b) := by
  simp only [avg, Finset.mul_sum, mul_add, Finset.sum_add_distrib]

private theorem avg_tsum {ι : Type*} (f : ι → Bool → Bool → ℝ≥0∞) :
    ∑' i, avg (f i) = avg (fun a b => ∑' i, f i a b) := by
  simp only [avg, ENNReal.tsum_mul_left, tsum_add]

private theorem avg_add (f g : Bool → Bool → ℝ≥0∞) :
    avg f + avg g = avg (fun a b => f a b + g a b) := by unfold avg; ring

/-- **Conservation up to a deadline.** The mass of every output first observed through
checkpoint $n$, plus the probability of still being live then, is exactly one. This finite-time
identity does not assume that the sampler eventually halts. -/
theorem stopped_add_live (n : ℕ) (c : Cfgₓ) :
    (∑ t ∈ Finset.range (n+1), ∑' y, M.hit y t c) + M.live n c = 1 := by
  classical
  induction n generalizing c with
  | zero => by_cases h : c.state = none <;> simp [hit, live, Cfg.Halted, h]
  | succ n ih =>
    rw [Finset.sum_range_succ']
    by_cases h : c.state = none
    · simp [hit, live, Cfg.Halted, h]
    · simp only [hit, live, Cfg.Halted, h, false_and, ite_false, tsum_zero, add_zero]
      simp_rw [avg_tsum, avg_sum, avg_add, ih]
      exact avg_const 1

/-- **Eventual output mass.** Sum the disjoint first-halt probabilities of the bitstring $y$
over all checkpoints, starting the sampler on the encoded input $x$. Diverging runs contribute
to no output. -/
noncomputable def mass (x y : Bits) := ∑' n, M.hit y n (Cfg.init M.start x)

/-- The exact output law on an input where the sampler halts almost surely. The normalization
proof is about its own eventual masses; no output distribution is chosen or rescaled. -/
noncomputable def law (x : Bits) (h : HasSum (M.mass x) 1) : PMF Bits := ⟨_, h⟩

open MetaMathlibExt.BitstringEncoding Cslib.Crypto.Framework

abbrev input (n : ℕ+) (aux : Bits) : Bits := bitEncode (List.replicate n.val true, aux)

/-- **Efficient exact sampler on a polynomial input envelope.** Fix one machine and one bound
$b$ on auxiliary bit lengths. It halts almost surely on every permitted input. There is one
polynomial $p$ and one nonnegative negligible error $\epsilon$ such that, for every positive
security parameter $n$ and every auxiliary string of length at most $b(n)$, its chance of
running beyond $2p(n)$ steps on the framed pair $(1^n,\mathrm{aux})$ is at most $\epsilon(n)$.
Almost-sure termination is a separate condition, not inferred from this tail inequality. -/
structure Efficient (b : Polynomial ℕ) : Prop where
  halts : ∀ (n : ℕ+) (aux : Bits), aux.length ≤ b.eval n.val → HasSum (M.mass (input n aux)) 1
  tail : ∃ (p : Polynomial ℕ) (ε : ℕ → ℝ), (∀ n, 0 ≤ ε n) ∧ NegligibleAdv ε ∧
    ∀ (n : ℕ+) (aux : Bits), aux.length ≤ b.eval n.val →
      M.live (p.eval n.val) (Cfg.init M.start (input n aux)) ≤ ENNReal.ofReal (ε n.val)

end FairSampler
/-- **A sampler with a uniform time guarantee.** One fair-bit table is fixed for all security
parameters and all auxiliary words up to its polynomial length envelope. It halts almost surely
and has a uniform negligible running-time tail on that entire envelope. -/
structure TailAlgorithm where
  machine : FairSampler
  bound : Polynomial ℕ
  efficient : machine.Efficient bound

/-- The given argument must fit the algorithm's envelope, and the mass of every output of the
actual local computation must equal that of the specified PMF, including zero off its support. -/
def TailAlgorithm.Realizes (A : TailAlgorithm) (n : ℕ+) (aux : Bits) (μ : PMF Bits) : Prop :=
  aux.length ≤ A.bound.eval n.val ∧ A.machine.mass (FairSampler.input n aux) = ⇑μ

end Cslib.Crypto.Framework
