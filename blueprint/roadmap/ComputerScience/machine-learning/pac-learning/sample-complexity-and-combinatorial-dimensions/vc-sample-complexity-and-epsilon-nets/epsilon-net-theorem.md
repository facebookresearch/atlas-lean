# The epsilon-net theorem

Let $Z$ be a countable set with all subsets measurable, $G$ a class of functions $Z \to \{0,1\}$ with growth function $\Pi_G$, $\mu$ a probability measure on $Z$, $\varepsilon > 0$ and $m \ge 1$ with $\varepsilon m \ge 8$. Then $m$ i.i.d. samples from $\mu$ fail to be an $\varepsilon$-net for $G$ with probability at most

$$
2\,\Pi_G(2m)\, 2^{-\lceil \varepsilon m/2 \rceil}.
$$

If every finite set shattered by $G$ has at most $d$ points, $\varepsilon \in (0,1)$, $\delta \in (0,1)$ and

$$
m \ge \frac{8}{\varepsilon}\Big(d \ln\frac{48}{\varepsilon} + \ln\frac{4}{\delta}\Big),
$$

the failure probability is at most $\delta$.

## Proof sketch

If some heavy $g$ misses the first sample, then by the Chernoff lower tail a second sample has at least $\lceil \varepsilon m/2 \rceil$ points with $g = 1$ with probability at least $1/2$, so the bad event costs at most twice the double-sample event. For a fixed double sample and a fixed restricted pattern with $k$ ones in the union, the fraction of swaps placing all $k$ ones in the second half is at most $2^{-k}$; a union bound over at most $\Pi_G(2m)$ patterns and swap counting finish, and Sauer's lemma gives the sample size.

## Depends on

- [Epsilon-net of a sample for a class of events](epsilon-net-of-a-sample.md)
- [Growth function](../../../../not-yet-classified/growth-function/growth-function.md)
- [The VC dimension is at most the size of the ground set](../../../../../Combinatorics/extremal-set-theory/vc-dim-le-card.md)

## Proof depends on

- [Double-sample symmetrization: ghost samples and coordinate swaps](double-sample-symmetrization.md)
- [Sauer bound for the growth function](../../../../not-yet-classified/growth-function/growth-function-le-sum.md)

## Sources

- D. Haussler and E. Welzl, "Epsilon-Nets and Simplex Range Queries", Discrete and Computational Geometry, 1987.
- A. Blumer, A. Ehrenfeucht, D. Haussler and M. K. Warmuth, "Learnability and the Vapnik-Chervonenkis Dimension", Journal of the ACM, 1989.
- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
