# Packing lower bound for approximate differential privacy

Let $M$ be $(\varepsilon, \delta)$-differentially private for Hamming adjacency, let datasets $x_j$ ($j \in J$) be within Hamming distance $m$ of a centre $x_0$, and let $B_j$ be pairwise disjoint events with $\Pr[M(x_j) \in B_j] \ge 1/2$. Then

$$
|J| \cdot \bigl(\tfrac12 - m\, e^{(m-1)\varepsilon}\delta\bigr) \le e^{m\varepsilon} .
$$

More generally, if an adjacency relates $x_0$ to each $x_j$ directly and $M(x_j)$ puts mass at least $\beta$ on $B_j$, then $|J|(\beta - \delta) \le e^{\varepsilon}$. For pure privacy ($\delta = 0$) this is the packing bound $|J| \le 2e^{m\varepsilon}$, which forces $m \ge (\ln|J| - \ln 2)/\varepsilon$.

## Proof sketch

Group privacy transfers the mass of $M(x_j)$ on $B_j$ to $M(x_0)$ with factor $e^{m\varepsilon}$ and additive $m e^{(m-1)\varepsilon}\delta$; disjointness bounds the sum of the masses of $M(x_0)$ by $1$.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)
- [Neighbouring row databases](../differential-privacy/hamming-adj.md)

## Proof depends on

- [Group privacy along a chain](../differential-privacy/group.md)
- [Packing lower bound for pure differential privacy](../differential-privacy/packing-lower-bound-for-pure-differential.md)

## Sources

- Cynthia Dwork and Aaron Roth, "The Algorithmic Foundations of Differential Privacy", Foundations and Trends in Theoretical Computer Science, 2014.
