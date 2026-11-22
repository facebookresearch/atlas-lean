/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Data.Fin.VecNotation

/-!
# Markov chain finite-dimensional distributions

If `X` is a sequence of random variables with transition kernel `κ`, in the
sense that for every `k`, every measurable `B`, and every `C` measurable
with respect to `σ(X₀, …, Xₖ)`,
`P(C ∩ {Xₖ₊₁ ∈ B}) = ∫_C κ(Xₖ ω) B dP`, then for any measurable sets
`A₀, …, Aₙ`,
`P(Xᵢ ∈ Aᵢ, 0 ≤ i ≤ n) = ∫_{A₀} μ(dx₀) ∫_{A₁} κ(x₀, dx₁) ⋯ ∫_{Aₙ} κ(xₙ₋₁, dxₙ)`
where `μ = P ∘ (X₀)⁻¹` is the initial distribution.

## Source

This formalizes the target "Theorem (Markov chain finite dimensional
distributions)" (Lecture 30/31) of
`v1/Atlas/TheoryOfProbability/targets.yaml`: "If `Xₙ` is any Markov chain
with initial distribution `μ` and transition `p`, then finite dimensional
probabilities are given by `P(Xⱼ ∈ Bⱼ, 0 ≤ j ≤ n) = ∫_{B₀} μ(dx₀)
∫_{B₁} p(x₀, dx₁) ⋯ ∫_{Bₙ} p(xₙ₋₁, dxₙ)`." Its v1 formalization is
`v1/Atlas/TheoryOfProbability/code/MarkovChainFDD.lean`
(`markov_chain_finite_dimensional_distributions`), ported here with no
statement change.

## Relation to Mathlib

Mathlib has the Ionescu–Tulcea trajectory measure
(`Kernel.trajMeasure`) and its conditional distributions
(`Kernel.condDistrib_trajMeasure`), but no finite-dimensional-distribution
formula for a general Markov chain: a search for `markovFDD` in Mathlib
finds nothing. The proof here is the v1 proof: promote the Markov property
from indicators to general measurable functions, then induct on `n`.

## Main results

* `MathlibExt.Probability.MarkovChainFDD.markovFDD`: the iterated-integral
  finite-dimensional distribution.
* `MathlibExt.Probability.MarkovChainFDD.markovFDD_measurable`:
  measurability of `markovFDD` in the starting state.
* `MathlibExt.Probability.MarkovChainFDD.markov_chain_finite_dimensional_distributions`:
  the book's finite-dimensional-distribution formula.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory ENNReal Set

namespace MathlibExt.Probability.MarkovChainFDD

/-- **Finite-dimensional distribution of a Markov chain.** For a measure $\mu$ on a measurable
space $S$, a kernel $\kappa$ from $S$ to $S$, a natural number $n$ and sets
$A_0, \dots, A_n \subseteq S$, the finite-dimensional distribution
$\mathrm{FDD}_n(\mu, \kappa; A_0, \dots, A_n) \in [0, \infty]$ is defined by recursion on $n$:
$\mathrm{FDD}_0(\mu, \kappa; A_0) = \mu(A_0)$ and
$\mathrm{FDD}_{n+1}(\mu, \kappa; A_0, \dots, A_{n+1}) =
\int_{A_0} \mathrm{FDD}_n(\kappa(x), \kappa; A_1, \dots, A_{n+1}) \, d\mu(x)$.
Unfolded, it is the iterated integral
$$
\int_{A_0} \mu(dx_0) \int_{A_1} \kappa(x_0, dx_1) \cdots \int_{A_n} \kappa(x_{n-1}, dx_n).
$$

When $\mu$ is a probability measure and $\kappa$ a Markov kernel, this is the probability that a
chain with initial distribution $\mu$ and transition kernel $\kappa$ visits $A_0, A_1, \dots, A_n$
at consecutive times. -/
noncomputable def markovFDD {S : Type*} [MeasurableSpace S]
    (mu : Measure S) (kappa : Kernel S S) : (n : Nat) -> (Fin (n + 1) -> Set S) -> ENNReal
  | 0, A => mu (A 0)
  | n + 1, A => ∫⁻ x in A 0, markovFDD (kappa x) kappa n (fun i => A i.succ) ∂mu

set_option maxHeartbeats 800000 in
/-- **Measurability of the finite-dimensional distributions in the starting state.** Let $\kappa$
be a Markov kernel on a measurable space $S$, let $n$ be a natural number and let
$A_0, \dots, A_n$ be measurable subsets of $S$. Write $\mathrm{FDD}_n(\mu, \kappa; A_0, \dots, A_n)$
for the finite-dimensional distribution of a Markov chain with initial measure $\mu$ and
transition kernel $\kappa$. Then the map
$x \mapsto \mathrm{FDD}_n(\kappa(x), \kappa; A_0, \dots, A_n)$ from $S$ to $[0, \infty]$ is
measurable.

This is the regularity needed to integrate the finite-dimensional distributions against a
starting distribution. -/
lemma markovFDD_measurable {S : Type*} [MeasurableSpace S]
    (kappa : Kernel S S) [IsMarkovKernel kappa]
    (n : Nat) (A : Fin (n + 1) -> Set S) (hA : forall i, MeasurableSet (A i)) :
    Measurable (fun x => markovFDD (kappa x) kappa n A) := by
  induction n with
  | zero => simp only [markovFDD]; exact Kernel.measurable_coe kappa (hA 0)
  | succ m ih =>
    simp only [markovFDD]
    show Measurable (fun x => ∫⁻ y in A 0, markovFDD (kappa y) kappa m (fun i => A i.succ) ∂(kappa x))
    have hg : Measurable (fun x => markovFDD (kappa x) kappa m (fun i => A i.succ)) :=
      ih (fun i => A i.succ) (fun i => hA i.succ)
    have : (fun x => ∫⁻ y in A 0, markovFDD (kappa y) kappa m (fun i => A i.succ) ∂(kappa x)) =
           (fun x => ∫⁻ y, (A 0).indicator
             (fun y => markovFDD (kappa y) kappa m (fun i => A i.succ)) y ∂(kappa x)) := by
      ext x; rw [← lintegral_indicator (hA 0)]
    rw [this]
    exact (Measurable.lintegral_kernel_prod_right ((hg.indicator (hA 0)).comp measurable_snd))

/-- **The σ-algebras generated by a sequence increase.** Let $X_0, X_1, \dots$ be maps from a
measurable space $\Omega$ to a measurable space $S$, and for each $k$ let $\sigma(X_0, \dots, X_k)$
be the σ-algebra on $\Omega$ generated by $\omega \mapsto (X_0(\omega), \dots, X_k(\omega))$, with
the product σ-algebra on $S^{k+1}$. Then
$\sigma(X_0, \dots, X_k) \subseteq \sigma(X_0, \dots, X_{k+1})$ for every $k$. -/
lemma comap_sigma_mono
    {Omega S : Type*} [MeasurableSpace Omega] [MeasurableSpace S]
    (X : Nat -> Omega -> S) (k : Nat) :
    MeasurableSpace.comap (fun omega => fun i : Fin (k + 1) => X i omega) MeasurableSpace.pi ≤
    MeasurableSpace.comap (fun omega => fun i : Fin (k + 2) => X i omega) MeasurableSpace.pi := by
  let phi : (Fin (k + 2) -> S) -> (Fin (k + 1) -> S) := fun f i => f (Fin.castSucc i)
  have hphi : @Measurable _ _ MeasurableSpace.pi MeasurableSpace.pi phi :=
    Measurable.of_eval (fun i => measurable_pi_apply _)
  have h_factor : (fun omega => fun i : Fin (k + 1) => X (↑i) omega) =
      phi ∘ (fun omega => fun i : Fin (k + 2) => X (↑i) omega) := by
    ext omega i; simp [phi, Fin.castSucc]
  rw [h_factor, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hphi.comap_le

/-- **Adding the next step to a past event.** Let $X_0, X_1, \dots$ be maps from a measurable space
$\Omega$ to a measurable space $S$, and write $\sigma(X_0, \dots, X_k)$ for the σ-algebra on
$\Omega$ generated by $\omega \mapsto (X_0(\omega), \dots, X_k(\omega))$, with the product
σ-algebra on $S^{k+1}$. If $C$ is measurable with respect to $\sigma(X_0, \dots, X_k)$ and
$B \subseteq S$ is measurable, then $C \cap X_{k+1}^{-1}(B)$ is measurable with respect to
$\sigma(X_0, \dots, X_{k+1})$. -/
lemma comap_inter_preimage
    {Omega S : Type*} [MeasurableSpace Omega] [MeasurableSpace S]
    (X : Nat -> Omega -> S) (k : Nat)
    (C : Set Omega) (B : Set S) (hB : MeasurableSet B)
    (hC : @MeasurableSet Omega (MeasurableSpace.comap
      (fun omega => fun i : Fin (k + 1) => X i omega) MeasurableSpace.pi) C) :
    @MeasurableSet Omega (MeasurableSpace.comap
      (fun omega => fun i : Fin (k + 2) => X i omega) MeasurableSpace.pi)
      (C ∩ X (k + 1) ⁻¹' B) := by
  exact MeasurableSet.inter (comap_sigma_mono X k C hC)
    (by rw [MeasurableSpace.measurableSet_comap]
        exact ⟨(fun f : Fin (k + 2) -> S => f ⟨k + 1, by omega⟩) ⁻¹' B,
          (measurable_pi_apply _) hB, by ext omega; simp⟩)

/-- **The Markov property for measurable functions.** Let $P$ be a probability measure on a
measurable space $\Omega$, let $X_0, X_1, \dots$ be measurable maps from $\Omega$ to a measurable
space $S$, and let $\kappa$ be a Markov kernel on $S$. Write $\sigma(X_0, \dots, X_k)$ for the
σ-algebra on $\Omega$ generated by $\omega \mapsto (X_0(\omega), \dots, X_k(\omega))$, with the
product σ-algebra on $S^{k+1}$. Suppose that for every $k$, every measurable $B \subseteq S$ and
every $C$ measurable with respect to $\sigma(X_0, \dots, X_k)$,
$\int_C \mathbf{1}_{X_{k+1}^{-1}(B)} \, dP = \int_C \kappa(X_k(\omega), B) \, dP(\omega)$.
Then for every $k$, every $C$ measurable with respect to $\sigma(X_0, \dots, X_k)$ and every
measurable $f : S \to [0, \infty]$,
$\int_C f(X_{k+1}(\omega)) \, dP(\omega) =
\int_C \int_S f(y) \, \kappa(X_k(\omega), dy) \, dP(\omega)$. -/
lemma lintegral_measurable_extension
    {Omega S : Type*} [MeasurableSpace Omega] [MeasurableSpace S]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : Nat -> Omega -> S) (hmeas : forall i, Measurable (X i))
    (kappa : Kernel S S) [IsMarkovKernel kappa]
    (hmarkov : forall (k : Nat) (B : Set S), MeasurableSet B ->
      forall (C : Set Omega),
        @MeasurableSet Omega (MeasurableSpace.comap
          (fun omega => fun i : Fin (k + 1) => X i omega) MeasurableSpace.pi) C ->
        ∫⁻ omega in C, (X (k + 1) ⁻¹' B).indicator (fun _ => (1 : ENNReal)) omega ∂P =
        ∫⁻ omega in C, kappa (X k omega) B ∂P)
    (k : Nat) (C : Set Omega)
    (hC_comap : @MeasurableSet Omega (MeasurableSpace.comap
      (fun omega => fun i : Fin (k + 1) => X i omega) MeasurableSpace.pi) C)
    (f : S -> ENNReal) (hf : Measurable f) :
    ∫⁻ omega in C, f (X (k + 1) omega) ∂P = ∫⁻ omega in C, (∫⁻ y, f y ∂kappa (X k omega)) ∂P := by
  have h_eq : (P.restrict C).map (X (k + 1)) =
      ((P.restrict C).map (X k)).bind (fun x => kappa x) := by
    ext B hB
    rw [Measure.map_apply (hmeas (k + 1)) hB,
        Measure.bind_apply hB (Kernel.measurable kappa).aemeasurable,
        lintegral_map (Kernel.measurable_coe kappa hB) (hmeas k),
        Measure.restrict_apply (hmeas (k + 1) hB)]
    have h := hmarkov k B hB C hC_comap
    rw [lintegral_indicator ((hmeas (k + 1)) hB), setLIntegral_one,
        Measure.restrict_apply ((hmeas (k + 1)) hB)] at h
    exact h
  calc ∫⁻ omega in C, f (X (k + 1) omega) ∂P
      = ∫⁻ y, f y ∂((P.restrict C).map (X (k + 1))) := by
          rw [lintegral_map hf (hmeas (k + 1))]
    _ = ∫⁻ y, f y ∂(((P.restrict C).map (X k)).bind (fun x => kappa x)) := by
          rw [h_eq]
    _ = ∫⁻ x, (∫⁻ y, f y ∂kappa x) ∂((P.restrict C).map (X k)) := by
          rw [Measure.lintegral_bind (Kernel.measurable kappa).aemeasurable hf.aemeasurable]
    _ = ∫⁻ omega in C, (∫⁻ y, f y ∂kappa (X k omega)) ∂P := by
          rw [lintegral_map _ (hmeas k)]
          exact Measurable.lintegral_kernel_prod_right (hf.comp measurable_snd)

/-- **Restricting an integral to a preimage.** Let $P$ be a measure on a measurable space $\Omega$,
let $X : \Omega \to S$ be a measurable map to a measurable space $S$, let $A \subseteq S$ be
measurable, let $C \subseteq \Omega$ be any set and let $f : S \to [0, \infty]$ be any function.
Then
$\int_{C \cap X^{-1}(A)} f(X(\omega)) \, dP(\omega) =
\int_C \mathbf{1}_A(X(\omega)) \, f(X(\omega)) \, dP(\omega)$. -/
lemma set_lintegral_inter_preimage
    {Omega S : Type*} [MeasurableSpace Omega] [MeasurableSpace S]
    (P : Measure Omega) (X : Omega -> S) (hX : Measurable X)
    (A : Set S) (hA : MeasurableSet A) (C : Set Omega)
    (f : S -> ENNReal) :
    ∫⁻ omega in C ∩ X ⁻¹' A, f (X omega) ∂P = ∫⁻ omega in C, A.indicator f (X omega) ∂P := by
  have : forall omega, A.indicator f (X omega) = (X ⁻¹' A).indicator (fun omega => f (X omega)) omega := fun _ => rfl
  simp_rw [this]
  rw [lintegral_indicator (hX hA), Measure.restrict_restrict (hX hA), inter_comm]

set_option maxHeartbeats 1600000 in
/-- **Finite-dimensional distributions given the past.** Let $P$ be a probability measure on a
measurable space $\Omega$, let $X_0, X_1, \dots$ be measurable maps from $\Omega$ to a measurable
space $S$, and let $\kappa$ be a Markov kernel on $S$. Write $\sigma(X_0, \dots, X_k)$ for the
σ-algebra on $\Omega$ generated by $\omega \mapsto (X_0(\omega), \dots, X_k(\omega))$, with the
product σ-algebra on $S^{k+1}$, and $\mathrm{FDD}_n(\mu, \kappa; A_0, \dots, A_n)$ for the
finite-dimensional distribution of a Markov chain with initial measure $\mu$ and transition
kernel $\kappa$. Suppose that for every $k$, every measurable $B \subseteq S$ and every $C$
measurable with respect to $\sigma(X_0, \dots, X_k)$,
$\int_C \mathbf{1}_{X_{k+1}^{-1}(B)} \, dP = \int_C \kappa(X_k(\omega), B) \, dP(\omega)$.
Then for all natural numbers $n$ and $j$, all measurable sets $A_0, \dots, A_n \subseteq S$ and
every measurable set $C \subseteq \Omega$ that is also measurable with respect to
$\sigma(X_0, \dots, X_j)$,
$$
P\Bigl(C \cap \bigcap_{i=0}^{n} X_{j+1+i}^{-1}(A_i)\Bigr) =
\int_C \mathrm{FDD}_n(\kappa(X_j(\omega)), \kappa; A_0, \dots, A_n) \, dP(\omega).
$$
-/
theorem markov_chain_fdd_aux
    {Omega S : Type*} [MeasurableSpace Omega] [MeasurableSpace S]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : Nat -> Omega -> S) (hmeas : forall i, Measurable (X i))
    (kappa : Kernel S S) [IsMarkovKernel kappa]
    (hmarkov : forall (k : Nat) (B : Set S), MeasurableSet B ->
      forall (C : Set Omega),
        @MeasurableSet Omega (MeasurableSpace.comap
          (fun omega => fun i : Fin (k + 1) => X i omega) MeasurableSpace.pi) C ->
        ∫⁻ omega in C, (X (k + 1) ⁻¹' B).indicator (fun _ => (1 : ENNReal)) omega ∂P =
        ∫⁻ omega in C, kappa (X k omega) B ∂P)
    (n : Nat) (j : Nat)
    (A : Fin (n + 1) -> Set S) (hA : forall i, MeasurableSet (A i))
    (C : Set Omega) (hC_meas : MeasurableSet C)
    (hC_comap : @MeasurableSet Omega (MeasurableSpace.comap
      (fun omega => fun i : Fin (j + 1) => X i omega) MeasurableSpace.pi) C) :
    P (C ∩ ⋂ i : Fin (n + 1), X (j + 1 + ↑i) ⁻¹' A i) =
    ∫⁻ omega in C, markovFDD (kappa (X j omega)) kappa n A ∂P := by
  induction n generalizing j C with
  | zero =>
    simp only [markovFDD]
    have h_fin1 : ⋂ i : Fin 1, X (j + 1 + ↑i) ⁻¹' A i = X (j + 1) ⁻¹' A 0 := by
      ext omega; simp [Fin.forall_fin_one]
    rw [h_fin1]
    have h := hmarkov j (A 0) (hA 0) C hC_comap
    rw [lintegral_indicator (hmeas (j + 1) (hA 0)), setLIntegral_one,
        Measure.restrict_apply (hmeas (j + 1) (hA 0))] at h
    rw [inter_comm]; exact h
  | succ m ih =>
    have h_split : (⋂ i : Fin (m + 2), X (j + 1 + ↑i) ⁻¹' A i) =
        (X (j + 1) ⁻¹' A 0) ∩ (⋂ i : Fin (m + 1), X (j + 2 + ↑i) ⁻¹' A i.succ) := by
      ext omega
      simp only [mem_iInter, mem_inter_iff, mem_preimage]
      constructor
      · intro h
        exact ⟨by have := h 0; simp at this; exact this,
          fun i => by
            have := h i.succ; simp only [Fin.val_succ] at this
            convert this using 2; omega⟩
      · intro ⟨h0, hs⟩ i
        refine Fin.cases (by simpa using h0) (fun i => ?_) i
        simp only [Fin.val_succ]
        have := hs i; convert this using 2; omega
    rw [h_split, ← inter_assoc]
    set C' := C ∩ X (j + 1) ⁻¹' A 0
    have hC'_meas : MeasurableSet C' := hC_meas.inter (hmeas (j + 1) (hA 0))
    have hC'_comap : @MeasurableSet Omega (MeasurableSpace.comap
        (fun omega => fun i : Fin (j + 2) => X i omega) MeasurableSpace.pi) C' :=
      comap_inter_preimage X j C (A 0) (hA 0) hC_comap
    rw [ih (j + 1) (fun i => A i.succ) (fun i => hA i.succ) C' hC'_meas hC'_comap]
    simp only [markovFDD]
    set f := fun x => markovFDD (kappa x) kappa m (fun i => A i.succ) with hf_def
    have hf_meas : Measurable f := markovFDD_measurable kappa m _ (fun i => hA i.succ)
    rw [set_lintegral_inter_preimage P (X (j + 1)) (hmeas (j + 1)) (A 0) (hA 0) C f]
    rw [lintegral_measurable_extension P X hmeas kappa hmarkov j C hC_comap
      ((A 0).indicator f) (hf_meas.indicator (hA 0))]
    congr 1; ext omega
    rw [← lintegral_indicator (hA 0)]

set_option maxHeartbeats 1600000 in
/-- Finite-dimensional distributions of a Markov chain. If `X` is a sequence of random
variables with transition kernel `κ` (in the sense expressed by `hmarkov`), then for any
measurable sets `A 0, …, A n`,

  `P(⋂ i : Fin (n+1), {X i ∈ A i}) = markovFDD (P ∘ X 0⁻¹) κ n A`.

This is the standard formula expressing the law of `(X 0, …, X n)` as an iterated integral
against the initial distribution and the transition kernel. -/
private theorem markov_chain_fdd
    {Omega S : Type*} [MeasurableSpace Omega] [MeasurableSpace S]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : Nat -> Omega -> S) (hmeas : forall i, Measurable (X i))
    (kappa : Kernel S S) [IsMarkovKernel kappa]
    (n : Nat) (A : Fin (n + 1) -> Set S) (hA : forall i, MeasurableSet (A i))
    (hmarkov : forall (k : Nat) (B : Set S), MeasurableSet B ->
      forall (C : Set Omega),
        @MeasurableSet Omega (MeasurableSpace.comap
          (fun omega => fun i : Fin (k + 1) => X i omega) MeasurableSpace.pi) C ->
        ∫⁻ omega in C, (X (k + 1) ⁻¹' B).indicator (fun _ => (1 : ENNReal)) omega ∂P =
        ∫⁻ omega in C, kappa (X k omega) B ∂P) :
    P (⋂ i : Fin (n + 1), X i ⁻¹' A i) = markovFDD (P.map (X 0)) kappa n A := by
  induction n with
  | zero =>
    simp only [markovFDD]
    have h_fin1 : ⋂ i : Fin 1, X (↑i) ⁻¹' A i = X 0 ⁻¹' A 0 := by
      ext omega; simp [Fin.forall_fin_one]
    rw [h_fin1, ← Measure.map_apply (hmeas 0) (hA 0)]
  | succ m ih =>
    simp only [markovFDD]
    have h_split : (⋂ i : Fin (m + 2), X (↑i) ⁻¹' A i) =
        (X 0 ⁻¹' A 0) ∩ (⋂ i : Fin (m + 1), X (0 + 1 + ↑i) ⁻¹' A i.succ) := by
      ext omega
      simp only [mem_iInter, mem_inter_iff, mem_preimage]
      constructor
      · intro h
        exact ⟨by have := h 0; simp at this; exact this,
          fun i => by
            have := h i.succ; simp only [Fin.val_succ] at this
            convert this using 2; omega⟩
      · intro ⟨h0, hs⟩ i
        refine Fin.cases (by simpa using h0) (fun i => ?_) i
        simp only [Fin.val_succ]
        have := hs i; convert this using 2; omega
    rw [h_split]
    have hC_meas : MeasurableSet (X 0 ⁻¹' A 0) := hmeas 0 (hA 0)
    have hC_comap : @MeasurableSet Omega (MeasurableSpace.comap
        (fun omega => fun i : Fin 1 => X i omega) MeasurableSpace.pi) (X 0 ⁻¹' A 0) := by
      rw [MeasurableSpace.measurableSet_comap]
      exact ⟨(fun f : Fin 1 -> S => f 0) ⁻¹' A 0,
        (measurable_pi_apply _) (hA 0), by ext omega; simp⟩
    rw [markov_chain_fdd_aux P X hmeas kappa hmarkov m 0
      (fun i => A i.succ) (fun i => hA i.succ)
      (X 0 ⁻¹' A 0) hC_meas hC_comap]
    rw [← setLIntegral_map (hA 0)
      (markovFDD_measurable kappa m _ (fun i => hA i.succ)) (hmeas 0)]

/-- **Finite-dimensional distributions of a Markov chain.** Let $P$ be a probability measure on a
measurable space $\Omega$, let $X_0, X_1, \dots$ be measurable maps from $\Omega$ to a measurable
space $S$, and let $\kappa$ be a Markov kernel on $S$. Write $\sigma(X_0, \dots, X_k)$ for the
σ-algebra on $\Omega$ generated by $\omega \mapsto (X_0(\omega), \dots, X_k(\omega))$, with the
product σ-algebra on $S^{k+1}$. Suppose $X$ is a Markov chain with transition kernel $\kappa$:
for every $k$, every measurable $B \subseteq S$ and every $C$ measurable with respect to
$\sigma(X_0, \dots, X_k)$,
$\int_C \mathbf{1}_{X_{k+1}^{-1}(B)} \, dP = \int_C \kappa(X_k(\omega), B) \, dP(\omega)$.
Let $\mu = P \circ X_0^{-1}$ be the initial distribution. Then for every natural number $n$ and
all measurable sets $A_0, \dots, A_n \subseteq S$,
$$
P(X_i \in A_i \text{ for } 0 \le i \le n) = \int_{A_0} \mu(dx_0) \int_{A_1} \kappa(x_0, dx_1)
\cdots \int_{A_n} \kappa(x_{n-1}, dx_n),
$$
where the right-hand side is the finite-dimensional distribution
$\mathrm{FDD}_n(\mu, \kappa; A_0, \dots, A_n)$ of a Markov chain with initial measure $\mu$ and
transition kernel $\kappa$. -/
theorem markov_chain_finite_dimensional_distributions
    {Omega S : Type*} [MeasurableSpace Omega] [MeasurableSpace S]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : Nat -> Omega -> S) (hmeas : forall i, Measurable (X i))
    (kappa : Kernel S S) [IsMarkovKernel kappa]
    (n : Nat) (A : Fin (n + 1) -> Set S) (hA : forall i, MeasurableSet (A i))
    (hmarkov : forall (k : Nat) (B : Set S), MeasurableSet B ->
      forall (C : Set Omega),
        @MeasurableSet Omega (MeasurableSpace.comap
          (fun omega => fun i : Fin (k + 1) => X i omega) MeasurableSpace.pi) C ->
        ∫⁻ omega in C, (X (k + 1) ⁻¹' B).indicator (fun _ => (1 : ENNReal)) omega ∂P =
        ∫⁻ omega in C, kappa (X k omega) B ∂P) :
    P (⋂ i : Fin (n + 1), X i ⁻¹' A i) = markovFDD (P.map (X 0)) kappa n A :=
  markov_chain_fdd P X hmeas kappa n A hA hmarkov

end MathlibExt.Probability.MarkovChainFDD
