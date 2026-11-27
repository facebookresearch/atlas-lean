# Rademacher complexity of VC classes without a logarithmic factor

Let $C$ be a class of functions $X \to \{0,1\}$ all of whose finite shattered sets have at most $d$ points, and $\sigma(C)$ its $\pm 1$-valued sign class. For every $m > 0$ and every sample of $m$ points, the empirical Rademacher complexity satisfies

$$
\hat{R}_S(\sigma(C)) \le 32\sqrt{\frac{d}{m}},
$$

and the same bound holds for the Rademacher complexity under any distribution on a finite domain. Consequently, on a finite domain, with probability at least $1 - \delta$ an empirical risk minimizer $A$ for $C$ satisfies $\mathrm{err}_D(A(S)) \le \mathrm{err}_D(c) + 32\sqrt{d/m} + \sqrt{2\ln(2/\delta)/m}$ for every $c \in C$: an excess error $O(\sqrt{(d + \ln(1/\delta))/m})$.

## Proof sketch

On a sample, sign patterns of two labelings at Hamming distance $t$ are at Euclidean distance $2\sqrt{t}$. A maximal separated set of labelings at Hamming scale $m/4^{n+1}$ is a Euclidean net at scale $\sqrt{m}/2^n$ with at most $2^{2d(2n+5)}$ points by Dudley's packing bound. Dyadic chaining with these nets and the trivial net $\{0\}$ at the top sums to $32\sqrt{d/m}$.

## Depends on

- [Empirical Rademacher complexity](../rademacher-complexity/rademacher-complexity.md)
- [Rademacher complexity of a VC class, explicit rate](../rademacher-complexity/rademacher-complexity-sign-patterns-le-v.md)
- [Dudley's entropy bound](../../../../Probability/high-dimensional-probability/generic-chaining-and-gaussian-processes/integral-i-sup-le-dudley.md)

## Proof depends on

- [Dudley's packing bound for classes of bounded VC dimension](../../pac-learning/sample-complexity-and-combinatorial-dimensions/packing-and-one-inclusion-graphs/dudley-packing-bound-for-vc-classes.md)
- [Rademacher and VC bounds for binary classification](rademacher-bounds-for-binary-classification.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
- R. Vershynin, "High-Dimensional Probability: An Introduction with Applications in Data Science", Cambridge University Press, 2018.
