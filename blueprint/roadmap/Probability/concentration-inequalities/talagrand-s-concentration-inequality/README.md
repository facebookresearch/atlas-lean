# Talagrand's concentration inequality

A convex, $1$-Lipschitz function of independent bounded random variables concentrates around its
median and its mean at the scale of the bound, with Gaussian tails and constants independent of
the dimension. McDiarmid's bounded-differences inequality gives fluctuations of order $\sqrt{n}$
for the same functions; convexity removes the dependence on $n$. In random matrix theory this makes
the operator norm and other convex spectral statistics concentrate.

Behind them stands Talagrand's convex-distance inequality (1995). For $A \subseteq \Omega^N$ and
$x \in \Omega^N$, the convex distance $f_c(A, x)$ is the Euclidean distance from $0$ to the convex
hull of the sets of coordinates along which $x$ can be changed into a point of $A$; for the
product probability $P = \mu^{\otimes N}$ of any probability measure $\mu$ on $\Omega$, $\int \exp(f_c(A, \cdot)^2/4)\,dP \le 1/P(A)$. For a
finite set $\Omega$ the inequality follows by Talagrand's induction on $N$.

- [Talagrand's concentration inequality around a median](talagrand-concentration-median.md)
- [Talagrand's concentration inequality around the mean](talagrand-concentration-mean.md)
- [Talagrand's set $U_A(x)$](convex-support.md)
- [Talagrand's convex distance](convex-distance.md)
- [Points of $A$ are at convex distance zero](convex-distance-eq-zero-of-mem.md)
- [The convex distance is at most the square root of the Hamming distance](convex-distance-le-sqrt-card.md)
- [Talagrand's convex-distance inequality](lintegral-exp-convex-distance-sq-le.md)
- [Tail form of the convex-distance inequality](measure-le-convex-distance-le.md)
- [Product weights](prod-weight.md)
- [Weight of a set](weight-of.md)
- [Section at the first coordinate](section-at.md)
- [Projection forgetting the first coordinate](projection.md)
- [Talagrand's geometric step](convex-distance-cons-sq-le.md)
- [Weighted Hölder inequality for two factors](sum-mul-rpow-mul-rpow-le.md)
- [Talagrand's numerical lemma](exists-exp-le-two-sub-mul-rpow.md)
- [Talagrand's convex-distance inequality on a product of finite sets](sum-exp-convex-distance-mul-weight-of-le.md)
- [Tail form on a product of finite sets](weight-of-le-convex-distance-mul-weight.md)
- [The convex-distance inequality for a finite probability space, measure form](lintegral-exp-convex-distance-sq-le-of-f.md)

## Related topics

- [McDiarmid's inequality](../mcdiarmid-s-inequality/README.md)
- [Operator norm of random matrices](../../high-dimensional-probability/operator-norm-of-random-matrices/README.md)
