/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Logic.Function.Iterate
public import MathlibExt.Combinatorics.InfiniteWord.WordFactorComplexity
public import MathlibExt.Dynamics.EventuallyPeriodicSequence

@[expose] public section

namespace MetaMathlibExt

/-! # Pansiot's factor-complexity classification -/

/--
**Pansiot's classification of the factor complexity of pure morphic words.** Let $A$ be a
finite alphabet, let $\sigma$ be a morphism of the free monoid on $A$ that is non-erasing
(no $\sigma(x)$ is empty), let $a \in A$, and let $w = w_0 w_1 w_2 \cdots$ be an infinite word
over $A$ that is a pure fixed point of $\sigma$ from $a$: $\sigma^n(a)$ is a prefix of $w$ for
every $n \ge 0$, and the length $|\sigma^n(a)|$ tends to infinity. Assume that every letter of
$A$ occurs in $w$ and that $w$ is not eventually periodic, and let $p_w$ be the factor
complexity of $w$. A letter $x$ is bounded if $|\sigma^n(x)|$ is bounded in $n$, and $\sigma$
is everywhere growing if no letter is bounded. Call $\sigma$ quasi-uniform if for some real
$\beta \ge 1$ every letter $x$ has $|\sigma^n(x)| = \Theta(\beta^n)$; polynomially diverging if
for some real $\beta > 1$ and some $\alpha : A \to \mathbb{N}$ that is not identically zero,
every letter $x$ has $|\sigma^n(x)| = \Theta(n^{\alpha(x)} \beta^n)$; and exponentially
diverging if there are letters $x_1, x_2$, natural numbers $\alpha_1, \alpha_2$ and reals
$\beta_1 \ne \beta_2$, both greater than $1$, with
$|\sigma^n(x_i)| = \Theta(n^{\alpha_i} \beta_i^n)$ for $i = 1, 2$. All asymptotics are as
$n \to \infty$. Then:
(i) if $\sigma$ is everywhere growing and quasi-uniform, then $p_w(n) = O(n)$;
(ii) if $\sigma$ is everywhere growing and polynomially diverging, then
$p_w(n) = \Theta(n \log \log n)$;
(iii) if $\sigma$ is everywhere growing and exponentially diverging, then
$p_w(n) = \Theta(n \log n)$;
(iv) if $\sigma$ is not everywhere growing and infinitely many factors of $w$ consist of
bounded letters only, then $p_w(n) = \Theta(n^2)$;
(v) if $\sigma$ is not everywhere growing and only finitely many factors of $w$ consist of
bounded letters only, then there are a finite alphabet $B$, a letter $b \in B$, an everywhere
growing morphism $\tau$ of the free monoid on $B$, an infinite word $v$ over $B$ that is a
pure fixed point of $\tau$ from $b$, and a non-erasing morphism $\varphi$ from the free monoid
on $B$ to the free monoid on $A$, such that $w$ is the image of $v$ under $\varphi$ (for every
$n$ the word $\varphi(v_0 \cdots v_{n-1})$ is a prefix of $w$, and its length tends to
infinity) and $p_w(n) = \Theta(p_v(n))$, where $p_v$ is the factor complexity of $v$.

The quoted statement omits the hypotheses that $w$ is not eventually periodic and that every
letter of $A$ occurs in $w$, which the $\Theta$ lower bounds need. Without the first, the
morphism $a \mapsto ab$, $b \mapsto b$ fails case (iv), since its fixed point $abbb\cdots$ has
only two factors of each positive length. Without the second, letters absent from $w$ can
change the growth class of $\sigma$ without changing $w$.

Source: Fabien Durand, Julien Leroy, and Gwenaël Richomme, "Do the Properties of an
S-adic Representation Determine Factor Complexity?", Journal of Integer Sequences 16
(2013), Article 13.2.6, Theorem [Pansiot] (label `thm: pansiot`), lines 267–283,
quoting J.-J. Pansiot,
<https://cs.uwaterloo.ca/journals/JIS/VOL16/Durand/durand2.tex>.
-/
public theorem_wanted pansiot_factor_complexity_classification
    {A : Type} [Fintype A]
    (σ : A → List A) (a : A) (w : ℕ → A) :
    let wordPrefix {X : Type} (u : ℕ → X) (n : ℕ) : List X :=
      List.ofFn fun i : Fin n => u i
    let iterWord {X : Type} (μ : X → List X) (n : ℕ) (x : X) : List X :=
      Nat.iterate (fun u : List X => u.flatMap μ) n [x]
    let nonErasing {X Y : Type} (μ : X → List Y) : Prop :=
      ∀ x, μ x ≠ []
    let pureFixedPoint {X : Type} (μ : X → List X) (x : X) (u : ℕ → X) : Prop :=
      (∀ n, iterWord μ n x = wordPrefix u (iterWord μ n x).length) ∧
        Filter.Tendsto (fun n => (iterWord μ n x).length) Filter.atTop Filter.atTop
    let boundedLetter {X : Type} (μ : X → List X) (x : X) : Prop :=
      ∃ C, ∀ n, (iterWord μ n x).length ≤ C
    let everywhereGrowing {X : Type} (μ : X → List X) : Prop :=
      ∀ x, ¬boundedLetter μ x
    let factor {X : Type} (u : ℕ → X) (v : List X) : Prop :=
      ∃ i : ℕ, v = List.ofFn fun j : Fin v.length => u (i + j)
    let factorComplexity {X : Type} [Finite X] (u : ℕ → X) (n : ℕ) : ℕ :=
      wordFactorComplexity u n
    let growthTheta {X : Type} (μ : X → List X) (x : X) (g : ℕ → ℝ) : Prop :=
      Asymptotics.IsTheta Filter.atTop
        (fun n => ((iterWord μ n x).length : ℝ)) g
    let quasiUniform {X : Type} (μ : X → List X) : Prop :=
      ∃ β : ℝ, 1 ≤ β ∧ ∀ x, growthTheta μ x (fun n => β ^ n)
    let polynomiallyDiverging {X : Type} (μ : X → List X) : Prop :=
      ∃ (β : ℝ) (α : X → ℕ), 1 < β ∧ α ≠ 0 ∧
        ∀ x, growthTheta μ x (fun n => (n : ℝ) ^ α x * β ^ n)
    let exponentiallyDiverging {X : Type} (μ : X → List X) : Prop :=
      ∃ (x₁ x₂ : X) (α₁ α₂ : ℕ) (β₁ β₂ : ℝ),
        1 < β₁ ∧ 1 < β₂ ∧ β₁ ≠ β₂ ∧
          growthTheta μ x₁ (fun n => (n : ℝ) ^ α₁ * β₁ ^ n) ∧
          growthTheta μ x₂ (fun n => (n : ℝ) ^ α₂ * β₂ ^ n)
    let morphicImage {X Y : Type} (coding : X → List Y) (u : ℕ → X)
        (v : ℕ → Y) : Prop :=
      Filter.Tendsto (fun n => ((wordPrefix u n).flatMap coding).length)
          Filter.atTop Filter.atTop ∧
        ∀ n, (wordPrefix u n).flatMap coding =
          wordPrefix v ((wordPrefix u n).flatMap coding).length
    nonErasing σ →
      pureFixedPoint σ a w →
      (∀ x : A, ∃ i, w i = x) →
      ¬IsEventuallyPeriodic w →
        ((everywhereGrowing σ ∧ quasiUniform σ) →
            Asymptotics.IsBigO Filter.atTop
              (fun n => (factorComplexity w n : ℝ)) (fun n => (n : ℝ))) ∧
        ((everywhereGrowing σ ∧ polynomiallyDiverging σ) →
            Asymptotics.IsTheta Filter.atTop
              (fun n => (factorComplexity w n : ℝ))
              (fun n => (n : ℝ) * Real.log (Real.log (n : ℝ)))) ∧
        ((everywhereGrowing σ ∧ exponentiallyDiverging σ) →
            Asymptotics.IsTheta Filter.atTop
              (fun n => (factorComplexity w n : ℝ))
              (fun n => (n : ℝ) * Real.log (n : ℝ))) ∧
        ((¬everywhereGrowing σ ∧
            Set.Infinite {v : List A | factor w v ∧ ∀ x ∈ v, boundedLetter σ x}) →
            Asymptotics.IsTheta Filter.atTop
              (fun n => (factorComplexity w n : ℝ)) (fun n => (n : ℝ) ^ 2)) ∧
        ((¬everywhereGrowing σ ∧
            Set.Finite {v : List A | factor w v ∧ ∀ x ∈ v, boundedLetter σ x}) →
          ∃ (B : Type) (_ : Fintype B) (b : B) (τ : B → List B) (v : ℕ → B)
              (coding : B → List A),
            everywhereGrowing τ ∧ nonErasing coding ∧ pureFixedPoint τ b v ∧
              morphicImage coding v w ∧
              Asymptotics.IsTheta Filter.atTop
                (fun n => (factorComplexity w n : ℝ))
                (fun n => (factorComplexity (X := B) v n : ℝ)))

end MetaMathlibExt
