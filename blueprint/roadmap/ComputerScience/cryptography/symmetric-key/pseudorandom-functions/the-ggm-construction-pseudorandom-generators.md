# The GGM construction: pseudorandom generators give pseudorandom functions

Let $S$ and $R$ be finite nonempty sets, let $G : S \to S \times S$ be a length-doubling generator and write $G(s) = (G_0(s), G_1(s))$. For $\ell \ge 1$ define $F : S \times \{0,1\}^\ell \to S$ by $F(k, x_1 \cdots x_\ell) = G_{x_\ell}(\cdots G_{x_2}(G_{x_1}(k)) \cdots)$. Let $Q \ge 1$ and let $A$ be a PRF adversary with coins in $R$: an adaptive oracle algorithm that makes at most $Q$ queries along every path, whatever the answers. Then

$$\mathrm{Adv}^{\mathrm{PRF}}[A, F] = \ell\, Q \cdot \mathrm{Adv}^{\mathrm{PRG}}[B, G]$$

for the distinguisher $B$ built from $A$ by the hybrid construction. $B$ draws a level $i < \ell$ and a query index $j < Q$ uniformly and runs $A$ once, answering its queries from a lazily filled table of pairs of labels for the children of the nodes at level $i$ of the evaluation tree: a node that enters the table at query $m$ gets a uniform pair if $m < j$, the challenge pair if $m = j$, and $G(s)$ for a uniform seed $s$ if $m > j$.

Adversaries are measured here by their number of queries alone. The source's requirement that $B$ have about the same running time as $A$ (an "elementary wrapper around $A$") is expressed by the explicit construction of $B$: it runs $A$ once, keeps a table of at most $Q$ entries and evaluates $G$ at most $\ell$ times per query of $A$.

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, [Section 4.6, Theorem 4.10](https://crypto.stanford.edu/~dabo/cryptobook/BonehShoup_0_4.pdf)
- Original construction: O. Goldreich, S. Goldwasser and S. Micali, "How to construct random functions", *Journal of the ACM* 33(4):792–807, 1986. The statement above follows Boneh and Shoup, Theorem 4.10; the attribution follows Vadhan, *Pseudorandomness*, chapter notes to Chapter 7.
- S. Vadhan, *Pseudorandomness*, Foundations and Trends in Theoretical Computer Science 7(1–3), 2012, chapter notes to Chapter 7
