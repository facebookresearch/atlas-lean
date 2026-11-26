# Haussler's sphere-packing bound for classes of bounded VC dimension

Let $P \subseteq \{0,1\}^m$ with $m \ge 1$ shatter no set of more than $d$ coordinates, and suppose any two distinct members of $P$ have Hamming distance at least $\varepsilon m$, where $0 < \varepsilon \le 1$. Then

$$
|P| \le e\,(d+1)\left(\frac{2e}{\varepsilon}\right)^{d}.
$$

Consequently, if every finite set shattered by a binary class $C$ has at most $d$ points, then for every $x \in X^m$ the realized labelings $C|_x$ admit a Hamming net of radius $\varepsilon m$ inside $C|_x$ with at most $e(d+1)(2e/\varepsilon)^d$ points. This sharpens the exponent $2d$ of Dudley's packing bound to the optimal $d$.

## Proof sketch

The key combinatorial input is a weighted edge-density inequality on the hypercube: for a nonnegative weight $\mu$ whose support shatters no set of more than $d$ coordinates, the sum over hypercube edges of $\min(\mu(f), \mu(f \oplus e_i))$ is at most $d \sum_f \mu(f)$, proved by coordinate shifting (the max and min of $\mu$ across a coordinate have supports shattering at most $d$ and $d-1$ coordinates). Applied to the projections of $P$ onto random $r$-tuples of coordinates, it shows that $((r+1)\varepsilon - 2d)|P|$ is at most $(r+1)\varepsilon$ times the expected size of a random projection, which is bounded by Sauer's lemma; optimizing $r$ gives the bound.

## Depends on

- [Dudley's packing bound for classes of bounded VC dimension](dudley-packing-bound-for-vc-classes.md)
- [The VC dimension is at most the size of the ground set](../../../../../Combinatorics/extremal-set-theory/vc-dim-le-card.md)

## Proof depends on

- [Edge density and bounded-outdegree orientations of one-inclusion graphs](one-inclusion-graph-edge-density.md)
- [Sauer bound for the growth function](../../../../not-yet-classified/growth-function/growth-function-le-sum.md)

## Sources

- D. Haussler, "Sphere Packing Numbers for Subsets of the Boolean n-Cube with Bounded Vapnik-Chervonenkis Dimension", Journal of Combinatorial Theory, Series A, 1995.
