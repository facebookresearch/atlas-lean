# Expected moments of a Wigner matrix converge to the semicircle moments

Let $(Z_{ij})_{i \le j}$ be independent real random variables such that the off-diagonal entries
$Z_{ij}$, $i < j$, are identically distributed, the diagonal entries $Z_{ii}$ are identically
distributed, all are centred, $\mathbb{E} Z_{ij}^2 = 1$ for $i < j$, and every entry has finite
moments of all orders. Let $X_N$ be the [normalised real Wigner matrix](wigner-matrix-real.md).
Then for every $k \ge 0$,

$$\mathbb{E}\Bigl[\frac{1}{N} \operatorname{tr} X_N^k\Bigr] \longrightarrow \int x^k \, d\sigma(x)
\qquad (N \to \infty),$$

the $k$-th moment of the semicircle law, which is the number of noncrossing pair partitions of
$\{1, \dots, k\}$.

Proof in the source: expand $\mathbb{E}\operatorname{tr} X_N^k$ as a sum over closed words
$i_1 i_2 \cdots i_k i_1$; centring kills words that cross some edge once, words visiting fewer than
$k/2 + 1$ vertices are negligible, and the remaining *Wigner words* (trees with every edge crossed
twice, $k$ even) are, up to relabelling, in bijection with Dyck paths, equivalently with noncrossing
pair partitions (Proposition 2.1.11), each contributing $1$ in the limit.

## Informally uses

- [Noncrossing pair partitions of $\{1, \dots, 2k\}$ are counted by the Catalan number $C_k$](../../../Combinatorics/set-partitions/noncrossing-partitions/noncrossing-pair-partitions-and-the-catalan-count/card-noncrossing-pair-partition-two-mul.md):
  the number of equivalence classes of Wigner words.
- [The moments of the semicircle law count noncrossing pair partitions](integral-pow-semicircle-real-eq-card-non.md):
  identifies the count with the semicircle moments.

## Sources

- G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010 (numbering of the authors' pre-publication manuscript (2009), https://www.math.nyu.edu/~zeitouni/cupbook.pdf), Lemma 2.1.6 under the assumptions (2.1.1)–(2.1.2); proof in §2.1.3.
