# Center-star alignment approximates sum-of-pairs within 2 − 2/k

Let $v_1, \dots, v_k$ be $k \ge 2$ strings and let $\delta$ be a symbol cost on the alphabet extended by the gap symbol that is a metric: $\delta(x, y) \ge 0$, $\delta(x, y) = \delta(y, x)$, $\delta(x, x) = 0$ (in particular the gap–gap cost is $0$), and $\delta(x, z) \le \delta(x, y) + \delta(y, z)$; let $D(v_i, v_j)$ be the optimal pairwise alignment cost. The center string $v_c$ minimizes $\sum_i D(v_c, v_i)$, and the center-star alignment $A_c$ is a multiple alignment consistent with the star tree centered at $v_c$, that is, inducing an optimal pairwise alignment of $v_c$ with each $v_j$; such an alignment consistent with any tree on the $k$ strings is computed in $O(k^2n^2)$ time for strings of length at most $n$. With $d(A)$ the sum-of-pairs cost and $A^*$ an optimal multiple alignment, the lecture notes of El-Kebir (Theorem 2), which present the result following Gusfield, prove

$$d(A_c) \le \frac{2(k-1)}{k}\, d(A^*),$$

so the ratio is less than $2$ whenever $d(A^*) > 0$, and $d(A_c) = 0$ when $d(A^*) = 0$.

The proof combines Lemma 1, $d_{A_c}(v_i, v_j) \le D(v_i, v_c) + D(v_c, v_j)$ by the triangle inequality applied column by column, which gives $2d(A_c) \le 2(k-1)\sum_j D(v_c, v_j)$, with $2d(A^*) \ge \sum_i\sum_j D(v_i, v_j) \ge k\sum_j D(v_c, v_j)$ by the choice of the center.

## Proof depends on

- [The SP score is the sum of the induced pairwise scores](../../../../Biology/bioinformatics/sequence-alignment/multiple-sequence-alignment/msa-score-eq-sum-induced.md)
- [The sum-of-pairs score is bounded by the pairwise optima](../../../../Biology/bioinformatics/sequence-alignment/multiple-sequence-alignment/msa-score-le-sum-nw-score.md)

## Expansion

1. Definitions: multiple alignments, induced pairwise alignments, the sum-of-pairs cost, and the triangle inequality for the symbol cost (with the gap–gap cost zero, so that induced alignments drop all-gap columns).
2. Theorem 1: an alignment consistent with a given tree, built by adding one string at a time, in $O(k^2n^2)$ time.
3. Lemma 1: the induced cost of two non-center strings is at most the sum of their optimal costs to the center.
4. The upper bound $2d(A_c) \le 2(k-1)\sum_jD(v_c, v_j)$ and the lower bound $2d(A^*) \ge k\sum_jD(v_c, v_j)$, combined into the ratio $2 - 2/k$.

## Sources

- M. El-Kebir, CS 466 Introduction to Bioinformatics, lecture notes for Lectures 10–12, University of Illinois at Urbana-Champaign, Fall 2018, Section 3.1, Definition 2, Theorems 1–2 and Lemma 1.
- Original result: D. Gusfield, Efficient methods for multiple sequence alignment with guaranteed error bounds, Bull. Math. Biol. 55 (1993), 141–154. <https://doi.org/10.1007/BF02460299> The bound and its proof follow El-Kebir's lecture notes.
