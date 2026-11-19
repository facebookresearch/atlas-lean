# Donsker's invariance principle

Let $X_0, X_1, \dots$ be independent, identically
distributed, measurable real random variables on a probability space $(\Omega, P)$ such that
$X_0$ is integrable, $\mathbb{E}[X_0^2] < \infty$, $\mathbb{E}[X_0] = 0$ and
$\operatorname{Var}(X_0) = 1$. Let $(B_t)_{t \ge 0}$ be a real Brownian motion on a probability
space $(\Omega', P')$: its finite-dimensional laws are those of Brownian motion and its paths are
$P'$-almost surely continuous. For $n \ge 1$ let $S_n$ be the polygonal partial-sum process of
the $X_i$, the random element of $C([0,1], \mathbb{R})$ that linearly interpolates the values
$(X_0 + \dots + X_{k-1})/\sqrt{n}$ at the times $k/n$ for $0 \le k \le n$. Then there is a random
element $Y$ of $C([0,1], \mathbb{R})$ defined on $\Omega'$ such that $P'$-almost surely
$Y(t) = B_t$ for all $t \in [0,1]$, and $S_n$ converges in distribution to $Y$ as $n \to \infty$.
Here $C([0,1], \mathbb{R})$ carries the topology of uniform convergence and its Borel
$\sigma$-algebra.

Proof: The route combines finite-dimensional convergence from the central limit theorem,
tightness from a maximal inequality and a modulus-of-continuity criterion, Prokhorov's theorem,
and uniqueness of laws on $C([0,1], \mathbb{R})$ from finite-dimensional distributions.

## Background

- [Existence of Brownian motion](../../stochastic-calculus/construction-and-sample-paths-of-brownian-motion/exists-is-brownian-real.md):
  the statement takes a Brownian motion $B$ as a hypothesis, and such a process exists, so the
  invariance principle is not vacuous.

## Sources

- M. D. Donsker, *An invariance principle for certain probability limit theorems*, Memoirs of the
  American Mathematical Society 6 (1951).
- Yu. V. Prokhorov, *Convergence of random processes and limit theorems in probability theory*,
  Theory of Probability and Its Applications 1 (1956), 157–214 (the extension to Polish spaces).
- P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley, 1999.
- O. Kallenberg, *Foundations of Modern Probability*, Springer. Lean is `C(Icc 0 1, ℝ)` polygonal process with `MemLp 2`, mean-zero variance-one standardization.
