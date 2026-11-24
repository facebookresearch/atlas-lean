# Edit distance has no strongly subquadratic algorithm unless SETH fails

Backurs and Indyk (2018, Theorem 5) prove: if the edit distance of two sequences of length $n$ over an alphabet of size $7$ can be computed in time $O(n^{2-\delta})$ for some $\delta > 0$, then the Orthogonal Vectors Problem with $|A| = |B| = N$ and $A, B \subseteq \{0, 1\}^d$ (decide whether some $x \in A$, $y \in B$ have $x \cdot y = 0$) can be solved in time $d^{O(1)} N^{2-\delta}$. As the source recalls (Section 2), a strongly subquadratic algorithm for Orthogonal Vectors would give an algorithm for CNF-SAT with $N$ variables and $M$ clauses in time $M^{O(1)} 2^{(1-\varepsilon)N}$, violating the Strong Exponential Time Hypothesis (SETH). Hence, assuming SETH, no algorithm computes edit distance in time $O(n^{2-\delta})$, while the fastest known exact algorithm cited by the source runs in time $O(n^2/\log^2 n)$.

## Expansion

1. Definitions: unit-cost edit distance, the Orthogonal Vectors Problem, and SETH; the reduction from CNF-SAT to Orthogonal Vectors.
2. Coordinate gadgets and Theorem 1 of the source: their edit distances distinguish orthogonal from non-orthogonal coordinate pairs.
3. Vector gadgets (Theorem 2) and the pattern construction (Theorems 3 and 4), so that the edit distance of the two composed sequences takes a smaller value exactly when an orthogonal pair exists.
4. The length bound of the construction and the conclusion, Theorem 5.

## Sources

- A. Backurs and P. Indyk, Edit distance cannot be computed in strongly subquadratic time (unless SETH is false), SIAM J. Comput. 47 (2018), 1087–1097, Theorems 1–5. <https://arxiv.org/abs/1412.0348>
- Original result: R. Williams, A new algorithm for optimal 2-constraint satisfaction and its implications, Theoret. Comput. Sci. 348 (2005), 357–365. <https://doi.org/10.1016/j.tcs.2005.09.023> The implication from strongly subquadratic Orthogonal Vectors to a faster CNF-SAT algorithm follows Backurs and Indyk, Section 2.
