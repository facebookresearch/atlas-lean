# Noncrossing pair partitions of $2k$ points are counted by the Catalan number $C_k$

For every $k \ge 0$, the number of noncrossing partitions of $\{0, \dots, 2k - 1\}$ all of whose
blocks have two elements is

$$C_k = \frac{1}{k+1}\binom{2k}{k},$$

the $k$-th Catalan number. For instance there are $C_2 = 2$ noncrossing pairings of four points,
$\{\{0,1\},\{2,3\}\}$ and $\{\{0,3\},\{1,2\}\}$, while $\{\{0,2\},\{1,3\}\}$ crosses.

In the moment method for Wigner's semicircle law this count is the limit of
$\frac{1}{N}\mathbb{E}\operatorname{tr} X_N^{2k}$, where $X_N = Y_N/\sqrt{N}$ for an $N \times N$
Wigner matrix $Y_N$ whose entries are centred with variance one: the equivalence classes, under
relabelling of the letters, of the contributing Wigner words are in bijection with noncrossing
pair partitions (Anderson, Guionnet and Zeitouni, Proposition 2.1.11), and the count matches [the
semicircle moments](../../../../Probability/high-dimensional-probability/wigner-s-semicircle-law/integral-pow-semicircle-real-eq-card-non.md).

## Informally uses

- [Noncrossing pair partitions are noncrossing perfect matchings](pair-partition-equiv-ncmatching.md):
  transfers the count to matchings.
- [Counting noncrossing perfect matchings](card-nc-matching.md): the count of matchings.

## Sources

- Greg W. Anderson, Alice Guionnet and Ofer Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010 (numbering of the authors' pre-publication manuscript (2009), https://www.math.nyu.edu/~zeitouni/cupbook.pdf), §2.1.1 (Catalan numbers count noncrossing partitions, Definition 2.1.4
  and the recursion after it) and Proposition 2.1.11 with its proof (noncrossing pair partitions
  of $\{1, \dots, k\}$ correspond to Dyck paths).
