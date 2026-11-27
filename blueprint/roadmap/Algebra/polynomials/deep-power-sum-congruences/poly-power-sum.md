# Power sums of a polynomial

For a polynomial $P$ over a commutative ring $A$, with
elementary symmetric functions $e_i = e_i(P)$, the power sums $p_n = p_n(P) \in A$ are defined
recursively: $p_0$ is the degree of $P$ as a natural number ($0$ for $P = 0$), and for
$n \ge 1$ Newton's identity holds:

$$p_n = \sum_{i=1}^{n-1} (-1)^{i-1} e_i\, p_{n-i} + (-1)^{n-1} n\, e_n.$$

If $P$ is monic and $P = (X - \alpha_1) \cdots (X - \alpha_d)$, then
$p_n = \alpha_1^n + \cdots + \alpha_d^n$ for every $n$.

## Sources

- S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum Congruences*, INTEGERS 24 (2024), Article A46, Sections 2.1 and 3.2 (Newton's identities, Macdonald I.2.11').
