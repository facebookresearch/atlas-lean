# Four-Russians edit distance in subquadratic time

Masek and Paterson (1980) show that the edit distance between strings $A$ and $B$ of lengths $n \ge m$ over a finite alphabet, with nonnegative real insertion, deletion and replacement costs that are all integral multiples of a single positive real number, can be computed in $O(n\max(1, m/\log n))$ steps; in particular $O(n^2/\log n)$ for two strings of length $n$. The time bound is for a random-access machine under the logarithmic cost criterion, and the paper states that the finite-alphabet and discreteness conditions are needed for the algorithm to achieve it. As in Section 1 of the source, each single-edit cost is first normalized to its minimum effective cost, the least total cost of a sequence of edits with the same effect (for example, a replacement costs at most the deletion plus the insertion it can be replaced by); normalization keeps the costs nonnegative integral multiples of the unit and leaves the edit distance unchanged, and the recurrence uses the normalized costs. The method splits the Wagner–Fischer edit matrix into square submatrices of side $t$, with $t$ a suitable constant multiple of $\log n$. A submatrix is determined by its starting value, its two initial step vectors (differences of adjacent entries along its first row and column) and its two substrings. Under the nonnegativity and discreteness hypotheses the steps lie in a finite set independent of the strings: they are bounded in absolute value by the largest insertion and deletion costs (Lemma 3), and are integral multiples of the common unit (Lemma 4). Algorithm Y precomputes the final step vectors of every possible submatrix, Algorithm Z assembles the matrix of steps from them, and the edit distance is the sum of the steps along a boundary path.

## Depends on

- [Edit distance algorithm](../../../ComputerScience/string-algorithms/edit-distance/edit-distance.md)
- [Edit distance under general letter costs](../../../ComputerScience/string-algorithms/edit-distance-with-general-costs/general-cost-edit-distance.md)

## Proof depends on

- [The Wagner-Fischer recurrence for general costs](../../../ComputerScience/string-algorithms/edit-distance-with-general-costs/wagner-fischer-general-costs.md)

## Expansion

1. Nonnegative costs and their normalization to minimum effective costs (Section 1), the Wagner–Fischer recurrence with the normalized costs (Theorems 1 and 2 of the source) and its restatement in terms of steps (Corollary 1).
2. Lemma 3: steps are bounded by the maximal insertion and deletion costs; Lemma 4: under discreteness there are finitely many possible steps.
3. Algorithm Y: enumeration of all pairs of substrings and step vectors of length $t$, and the cost $O(c^t t^2\log t)$ of precomputing their final step vectors.
4. Algorithm Z (Section 2.2): assembly with $\lceil n/t\rceil\lceil m/t\rceil$ block fetches of length-$t$ vectors at cost $O(t + \log n)$ each, covering both $m \ge t$ and $m < t$, and the choice of $t$ of order $\log n$ giving the bound $O(n\max(1, m/\log n))$; padding when $t$ does not divide the lengths.
5. Recovery of an optimal edit path (Section 2.3), and the role of the discreteness and finite-alphabet conditions.

## Sources

- W. J. Masek and M. S. Paterson, A faster algorithm computing string edit distances, J. Comput. System Sci. 20 (1980), 18–31, Sections 1–2, Lemmas 3–4. <https://doi.org/10.1016/0022-0000(80)90002-1>
