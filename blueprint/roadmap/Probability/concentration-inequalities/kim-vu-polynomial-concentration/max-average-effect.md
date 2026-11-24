# Maximal average effect of $j$ variables

For independent $\{0,1\}$ variables $t_i$ with means $p_i$ and a positive polynomial $Y_H$,

$$E_j(H) = \max_{|A| = j} \mathbb E\big[Y_{H_A}\big],$$

the largest expected [partial derivative](truncated-poly.md) with respect to $j$ variables: the maximal average effect of a group of $j$ variables (and $E_j(H) = 0$ for $j > n$, when there is no such set $A$). $E_0(H) = \mathbb E Y_H$; Kim and Vu set $E(H) = \max_{j \ge 0} E_j(H)$ and $E'(H) = \max_{j \ge 1} E_j(H)$. For triangles in $G(n, p)$: $E_0 = \binom n3 p^3$, $E_1 = (n - 2) p^2$, $E_2 = p$, $E_3 = 1$.

## Sources

- J. H. Kim and V. H. Vu, "Concentration of multivariate polynomials and its applications", *Combinatorica* 20 (2000), 417–434, Sections 1.2 and 1.3.
