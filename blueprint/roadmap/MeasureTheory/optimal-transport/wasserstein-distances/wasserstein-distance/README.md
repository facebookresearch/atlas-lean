# Wasserstein distance

For probability measures $\mu$ and $\nu$ on a metric space $(X, d)$ and an exponent $p \ge 1$, the
Wasserstein distance of order $p$ is

$$W_p(\mu, \nu) = \Bigl( \inf_\pi \int_{X \times X} d(x, y)^p \, d\pi(x, y) \Bigr)^{1/p} \in [0, \infty],$$

the infimum running over all couplings $\pi$ of $\mu$ and $\nu$. It is finite on the measures with
finite $p$-th moment. The same formula, $W_p = C_p^{1/p}$ with $C_p$ the infimum above, is
taken for every real $p$ and on any pseudo-extended metric space with a $\sigma$-algebra, with the
conventions of real powers in $[0, \infty]$ ($t^0 = 1$; $0^r = \infty$ and $\infty^r = 0$ for
$r < 0$) and $1/0 = 0$, so that $W_0 = C_0^0 = 1$. Each statement names the exponents and the
hypotheses on the space it needs.

## Idea

For $p \ge 1$ on a Polish metric space with its Borel sets, $W_p^p$ is the cheapest cost of moving
the mass of $\mu$ onto that of $\nu$ when moving a unit of mass by a distance $r$ costs $r^p$, and
$W_p$ is its $p$-th root. Unlike the total variation distance it sees the geometry: the distance
between Dirac masses at $x$ and $y$ is $d(x, y)$. The metric axioms come from operations on
couplings. Swapping the coordinates gives symmetry, the diagonal coupling gives
$W_p(\mu, \mu) = 0$, and gluing two couplings along their common marginal gives the triangle
inequality. Testing against Lipschitz functions shows that $W_p$ separates Borel probability
measures, and Hölder's inequality makes $W_p$ nondecreasing in $p$. Each statement below gives the
exponents and the spaces for which it holds.

## Statements

- [Wasserstein distance of order $p$](wasserstein.md)
- [Optimal transport cost of order $p$](transport-cost.md): the infimum in the definition.
- [Wasserstein distance as an infimum over couplings](wasserstein-eq-i-inf.md): the definition as one formula, for $p > 0$.
- [Every coupling bounds the transport cost](transport-cost-le-of-is-coupling.md): a basic fact of the definition.
- [Every coupling bounds the Wasserstein distance](wasserstein-le-of-is-coupling.md): a basic fact of the definition, for $p \ge 0$.
- [Diagonal coupling](is-coupling-diag.md): used to show that $W_p(\mu, \mu) = 0$.
- [Swapped coupling](is-coupling-swap.md): used for symmetry.
- [The product coupling](is-coupling-prod.md): used for finiteness.
- [Gluing lemma](exists-gluing.md): used for the triangle inequality.
- [The Wasserstein distance vanishes on the diagonal](wasserstein-self.md): a metric axiom, for $p > 0$.
- [Symmetry of the Wasserstein distance](wasserstein-comm.md): a metric axiom, for every real $p$.
- [Triangle inequality for the Wasserstein distance](wasserstein-triangle.md): a metric axiom, for $p \ge 1$ on a standard Borel space.
- [The Wasserstein distance separates probability measures](eq-of-wasserstein-eq-zero.md): a metric axiom, for $p \ge 1$ and Borel probability measures.
- [The Wasserstein distance is finite on measures with finite $p$-th moments](wasserstein-lt-top.md): finiteness on measures with finite $p$-th moment, for $p \ge 1$.
- [Wasserstein distance between Dirac masses](wasserstein-dirac.md): an example: Dirac masses, for $p > 0$.
- [Monotonicity of the Wasserstein distances in the exponent](wasserstein-mono.md): a comparison between exponents $0 < p \le q$.

## Sources

- C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften 338, Springer, 2009, Chapter 6.
