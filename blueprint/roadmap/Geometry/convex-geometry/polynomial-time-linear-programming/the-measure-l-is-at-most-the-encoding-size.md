# The measure L exceeds the encoding size by at most a constant

For every linear program $\min\{c^\top x : A x = b,\ x \ge 0\}$ with an integer $m \times n$ matrix $A$, $m, n \ge 1$, and integer vectors $b$, $c$, the measure $L$ of [the encoding size page](encoding-size-of-a-linear-program.md) satisfies

$$L \le \mathrm{size}(LP) + 4 - mn \le \mathrm{size}(LP) + 3 .$$

Hence an algorithm whose running time is polynomial in $L$ runs in time polynomial in the encoding size of its input. The proof bounds each term of $L$:

- by Hadamard's inequality, every square submatrix $A'$ of $A$ has $|\det A'| \le \prod_i \bigl(\sum_j |a'_{ij}|^2\bigr)^{1/2} \le \prod_{i,j} (1 + |a_{ij}|)$, the last product over all entries of $A$; so $\det_{\max} + 1 \le 2 \prod_{i,j} (1 + |a_{ij}|)$ and $\mathrm{size}(\det_{\max}) \le 2 + \sum_{i,j} \lceil \log_2(1 + |a_{ij}|) \rceil = 2 + \mathrm{size}(A) - mn$;
- every entry has size at least $1$, so $\mathrm{size}(b_{\max}) \le \mathrm{size}(b) - (m - 1)$ and $\mathrm{size}(c_{\max}) \le \mathrm{size}(c) - (n - 1)$.

Adding $m + n$ gives the bound. The strict inequality $L < \mathrm{size}(LP)$ printed in the source fails already for $A = (1)$, $b = (1)$, $c = (1)$, where $\mathrm{size}(LP) = 6$ and $L = 8$: its proof bounds the logarithms but not the sign bit that the size of each entry includes.

## Depends on

- [Encoding size of a linear program](encoding-size-of-a-linear-program.md)

## Proof depends on

- [Hadamard's determinant inequality](../../../LinearAlgebra/positive-definite-matrices/hadamard-s-inequality-and-determinant-bounds-for/hadamard-s-determinant-inequality/hadamard-determinant-inequality.md)

## Sources

- M. X. Goemans, *Linear Programming*, lecture notes for 18.415/6.854 Advanced Algorithms, MIT, October 1994, <https://www.cs.cmu.edu/afs/cs/user/glmiller/public/Scientific-Computing/F-11/RelatedWork/Goemans-LP-notes.pdf>, Section 11.1, Proposition 13 and the lemma before its proof (the polynomial relation between $L$ and the encoding size; the constant here is computed directly).
