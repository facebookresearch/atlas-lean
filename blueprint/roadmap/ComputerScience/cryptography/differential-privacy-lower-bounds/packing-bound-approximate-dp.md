# Packing lower bound for approximate differential privacy

Let $M$ be $(\varepsilon, \delta)$-differentially private for Hamming adjacency, let datasets $x_j$ ($j \in J$) be within Hamming distance $m$ of a centre $x_0$, and let $B_j$ be pairwise disjoint events with $\Pr[M(x_j) \in B_j] \ge p$ for every $j \in J$. Then

$$
|J| \cdot \bigl(p\, e^{-m\varepsilon} - m\delta\bigr) \le 1 .
$$

For pure privacy ($\delta = 0$) and $p = 1/2$ this is the packing bound $|J| \le 2e^{m\varepsilon}$, which forces $m \ge (\ln|J| - \ln 2)/\varepsilon$.

## Proof sketch

Group privacy (in the form $(k\varepsilon, k e^{k\varepsilon}\delta)$ for datasets at distance $k$) gives $\Pr[M(x_0) \in B_j] \ge p\, e^{-m\varepsilon} - m\delta$ for every $j$; disjointness bounds the sum of these masses of $M(x_0)$ by $1$. With Dwork and Roth's sharper group-privacy constant $(k\varepsilon, k e^{(k-1)\varepsilon}\delta)$ the same argument gives $|J|\bigl(p - m e^{(m-1)\varepsilon}\delta\bigr) \le e^{m\varepsilon}$, a derived variant not stated in the cited sources.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)
- [Neighbouring row databases](../differential-privacy/hamming-adj.md)

## Proof depends on

- [Group privacy along a chain](../differential-privacy/group.md)
- [Packing lower bound for pure differential privacy](../differential-privacy/packing-lower-bound-for-pure-differential.md)

## Sources

- Salil Vadhan, "The Complexity of Differential Privacy", in Tutorials on the Foundations of Cryptography, Springer, 2017, Chapter 7, Lemma 7.2.2 (group privacy, p. 360) and Theorem 7.5.13 with its proof (packing lower bound, p. 391); these are Lemma 2.2 and Theorem 5.13 of the 2016 manuscript. The inequality above is the one established in the proof of Theorem 7.5.13; the theorem's display prints $\delta$ for $m\delta$ in both versions.
- Cynthia Dwork and Aaron Roth, "The Algorithmic Foundations of Differential Privacy", Foundations and Trends in Theoretical Computer Science, 2014, Theorem 2.2 and Lemma 8.4.
