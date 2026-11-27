# Irreducibly diagonally dominant matrices are nonsingular

Let $A$ be an [irreducible](irreducible-matrix.md) $n \times n$ complex matrix that is weakly row diagonally dominant, $|a_{ii}| \ge \sum_{j \ne i} |a_{ij}|$ for every $i$, with strict inequality for at least one $i$. Then $A$ is nonsingular.

If $Ax = 0$ with $\max_i |x_i| = |x_m| = 1$, then $|a_{mm}| \le \sum_{j \ne m} |a_{mj}|\,|x_j| \le \sum_{j \ne m} |a_{mj}| \le |a_{mm}|$, so equality holds and $|x_j| = 1$ whenever $a_{mj} \ne 0$; irreducibility carries this along paths to every row, giving $|a_{ii}| = \sum_{j \ne i} |a_{ij}|$ for every $i$, a contradiction. The same holds with column sums, since $A^{\mathsf T}$ is irreducible exactly when $A$ is. The strictly diagonally dominant case needs no irreducibility (the Lévy–Desplanques theorem, in Mathlib as [det_ne_zero_of_sum_row_lt_diag](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/LinearAlgebra/Matrix/Gershgorin.lean#L63 "det_ne_zero_of_sum_row_lt_diag")).

## Depends on

- [Irreducible matrix](irreducible-matrix.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 4.2.3, Corollary 4.8 and the argument of the proof of Theorem 4.7, applied here directly to a null vector; the proof of Corollary 4.8 there argues instead through the position of $0$ relative to the union of the Gershgorin discs. Definition 4.5 there states diagonal dominance with column sums while the proofs of Theorem 4.7, Corollary 4.8 and Theorem 4.9 use row sums; the row form is stated here. <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
