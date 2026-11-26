# Donsker's invariance principle

Let $X_0, X_1, \dots$ be independent, identically distributed, measurable real random variables on a
probability space $(\Omega, P)$ with $\mathbb{E}[X_0^2] < \infty$, $\mathbb{E}[X_0] = 0$ and
$\operatorname{Var}(X_0) = 1$. For $n \ge 1$ let $S_n$ be the polygonal partial-sum process: the random
element of $C([0,1], \mathbb{R})$ that takes the value $(X_0 + \dots + X_{k-1})/\sqrt{n}$ at time $k/n$
for $0 \le k \le n$ and is linear in between. Let $(B_t)_{t \ge 0}$ be a real Brownian motion on a
probability space $(\Omega', P')$: its finite-dimensional laws are those of Brownian motion and its
paths are $P'$-almost surely continuous. Then there is a random element $Y$ of $C([0,1], \mathbb{R})$
defined on $\Omega'$ such that $P'$-almost surely $Y(t) = B_t$ for all $t \in [0,1]$, and $S_n$
converges in distribution to $Y$ as $n \to \infty$, where $C([0,1], \mathbb{R})$ carries the topology
of uniform convergence and its Borel $\sigma$-algebra. In short, the rescaled random walk converges in
law to Brownian motion on $[0,1]$.

## Idea

The central limit theorem describes the walk at one time; Donsker's theorem describes its whole path.
After time is rescaled by $n$ and space by $\sqrt{n}$, the random walk with steps $X_i$ converges to
Brownian motion whatever the law of the steps, as long as they are centred with unit variance: hence
the name invariance principle. For every continuous functional $f$ on $C([0,1], \mathbb{R})$, such as
the maximum of the path, $f(S_n)$ then converges in law to $f(B)$, so a limit computed for one walk,
or for Brownian motion, holds for all such walks. The proof has two parts: the finite-dimensional
distributions converge by the central limit theorem, and the laws of $S_n$ are tight, by a maximal
inequality (Etemadi's) and a modulus-of-continuity criterion. Prokhorov's theorem then gives limit
points, and finite-dimensional laws identify them.

## Statements

- [Donsker's invariance principle](donsker-invariance-principle.md)
- [Polygonal partial-sum process](donsker-process.md): definition used in the main statement
- [Explicit formula for the polygonal partial-sum process](donsker-process-apply-eq.md): lemma used in the proof of the main statement
- [Polygonal interpolation weight](donsker-weight.md): definition used by the polygonal process
- [Polygonal interpolation weight as a continuous function](donsker-weight-cm.md): definition used by the polygonal process
- [Clamping to the unit interval](donsker-clamp.md): definition used by the interpolation weight
- [Inclusion of the unit interval into the nonnegative reals](icc-to-nnreal.md): definition used in the main statement
- [Etemadi's maximal inequality](etemadi-maximal-inequality.md): Etemadi's maximal inequality, used for tightness
- [Finite-dimensional distributions determine laws on continuous paths](continuous-map-measure-ext-of-finset-eva.md): the uniqueness step that identifies limit laws on $C[0,1]$ in the classical proof

## Background

- [Lindeberg–Feller central limit theorem](../lindeberg-feller-central-limit-theorem/README.md): gives
  the convergence of the finite-dimensional distributions.
- [Tight families of probability measures](../../convergence-of-measures/tightness-of-probability-measures/README.md):
  the compactness half of the proof.
- [Weak convergence in the space of continuous functions](../../convergence-of-measures/weak-convergence-in-the-space-of-continuous-func/README.md):
  the mode of convergence in the conclusion.

## Sources

- M. D. Donsker, "An invariance principle for certain probability limit theorems", Memoirs of the
  American Mathematical Society (1951).
