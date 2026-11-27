# The GGM construction: pseudorandom generators give pseudorandom functions

Let $S$ and $R$ be finite nonempty sets, let $G : S \to S \times S$ be a length-doubling generator and write $G(s) = (G_0(s), G_1(s))$. For $\ell \ge 1$ define $F : S \times \{0,1\}^\ell \to S$ by $F(k, x_1 \cdots x_\ell) = G_{x_\ell}(\cdots G_{x_2}(G_{x_1}(k)) \cdots)$. Let $Q \ge 1$ and let $A$ be a PRF adversary: an adaptive oracle algorithm, run on coins drawn uniformly from $R$ independently of the key and of the random function, that makes at most $Q$ queries along every path, whatever the answers. Then

$$\mathrm{Adv}^{\mathrm{PRF}}[A, F] = \ell\, Q \cdot \mathrm{Adv}^{\mathrm{PRG}}[B, G]$$

for the distinguisher $B$ built from $A$ by the hybrid construction. $B$ draws a level $i < \ell$ and a query index $j < Q$ uniformly and runs $A$ once, answering its queries from a lazily filled table of pairs of labels for the children of the nodes at level $i$ of the evaluation tree: a node that enters the table at query $m$ gets a uniform pair if $m < j$, the challenge pair if $m = j$, and $G(s)$ for a uniform seed $s$ if $m > j$.

$B$ runs $A$ once, keeps at most $Q$ table entries and evaluates $G$ at most $\ell - i$ times per query. The equality is one between advantages for fixed finite sets and states no running time; the running-time requirement on $B$ and the asymptotic statement that $F$ is a secure PRF when $G$ is a secure PRG are outside it. Under Boneh and Shoup's efficiency assumptions ($S$ efficiently represented and sampleable, $G$ efficient, and $\ell$ and $Q$ polynomially bounded in the security parameter), this $B$ is an elementary wrapper around $A$ (Definition 2.12). For $Q = 0$ the adversary makes no queries and its advantage is $0$; the assumption $Q \ge 1$ only makes the coin set of $B$ nonempty.

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, [Section 4.6, Theorem 4.10, and Section 2.4.3, Definition 2.12](https://crypto.stanford.edu/~dabo/cryptobook/BonehShoup_0_4.pdf)
- Original construction: O. Goldreich, S. Goldwasser and S. Micali, "How to construct random functions", *Journal of the ACM* 33(4):792–807, 1986. The statement above follows Boneh and Shoup, Theorem 4.10; the attribution follows Vadhan, *Pseudorandomness*, chapter notes to Chapter 7.
- S. Vadhan, *Pseudorandomness*, Foundations and Trends in Theoretical Computer Science 7(1–3), 2012, chapter notes to Chapter 7
