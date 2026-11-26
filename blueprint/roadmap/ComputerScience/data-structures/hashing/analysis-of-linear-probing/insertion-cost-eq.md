# Knuth's exact mean insertion cost for linear probing

Let $1 \le k \le N$. Enter $k$ items into a cyclic table of $N$ cells by linear probing, with
independent uniform hash addresses. The [expected number of probes](insertion-cost.md) made by the
$k$-th item is

$$M(N, k) = \frac{1}{2}\bigl(1 + E_1(N, k)\bigr), \qquad
E_1(N, k) = \sum_{j=0}^{k-1} (j + 1)\frac{(k-1)(k-2)\cdots(k-j)}{N^j},$$

with $E_1$ one of [Knuth's auxiliary sums](knuth-e.md). This is Theorem 2 of Knuth's 1963 note,
third form. For example $M(5, 4) = 257/125$, an entry of the note's table for $N = 5$. In terms
of the number $k - 1$ of items already present, $M(N, k)$ is the expected cost of an insertion
into a table holding $k - 1$ items.

Knuth's proof goes through the probability $P(N, k, m)$ that the $k$-th item needs $m$
comparisons (Theorem 1 of the note) and Abel's generalized binomial theorem.

## Informally uses

- [Number of hash sequences without overflow](card-lin-success.md): Lemma 1, the first step of
  Knuth's computation of $P(N, k, m)$.

## Sources

- D. E. Knuth, "Notes on 'open' addressing", 22 July 1963, typeset by H. Prodinger in 1997,
  Section 5, Theorem 2: https://jeffe.cs.illinois.edu/teaching/datastructures/2011/notes/knuth-OALP.pdf
