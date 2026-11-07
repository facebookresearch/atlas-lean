# A- and Z-sequence characterization of integer Riordan arrays

Let $(d_{n,k})_{n,k \ge 0}$ be
an integer matrix that is lower triangular, that is, $d_{n,k} = 0$ whenever $n < k$. Then the
following are equivalent: (i) there are power series $g, f \in \mathbb{Z}[[x]]$ with $g(0) = 1$,
$f(0) = 0$ and $[x^1]\, f \ne 0$ such that $d_{n,k} = [x^n]\, g f^k$ for all $n, k \ge 0$;
(ii) $d_{0,0} = 1$ and there are rational sequences $(A_j)_{j \ge 0}$ and $(Z_j)_{j \ge 0}$ with
$A_0 \ne 0$ such that, for all $n, k \ge 0$,

$$d_{n+1,k+1} = \sum_{j=0}^{n} A_j\, d_{n,k+j} \quad\text{and}\quad
d_{n+1,0} = \sum_{j=0}^{n} Z_j\, d_{n,j}.$$

The sequences are rational because $A_0 = [x^1]\, f$ need not be a unit in $\mathbb{Z}$.

Correction to the cited source: Barry's Proposition displays the hypothesis $Z_0 \ne 0$, but the
identity Riordan array has $Z_0 = 0$, so that condition cannot hold in general. This statement
therefore drops $Z_0 \ne 0$ — a deliberate correction to the source, not just a normalization —
and instead imposes the Riordan normalization $d_{0,0} = 1$.

Proof: The forward implication uses coefficientwise triangular expansions in powers of $f$; the
converse reconstructs $g$ and $f$ from columns zero and one and proves rowwise uniqueness. This is
the route of Barry's Proposition Char following He and Sprugnoli's Theorems 2.1 and 2.2.

## Sources

- P. Barry, *A Note on a Family of Generalized Pascal Matrices Defined by Riordan Arrays*, Journal of Integer Sequences 16 (2013), Article 13.5.4, Proposition Char, lines 173-180, <https://cs.uwaterloo.ca/journals/JIS/VOL16/Barry2/barry231.tex>, after Theorems 2.1 and 2.2 of He.
