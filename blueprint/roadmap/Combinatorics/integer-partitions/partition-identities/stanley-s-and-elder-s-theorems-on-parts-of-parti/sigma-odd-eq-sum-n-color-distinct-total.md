# Odd-divisor sum via distinct $n$-color partitions and signed partition counts

For
$r \ge 0$ let $C_o(D, r)$ (resp. $C_e(D, r)$) be the total number of parts over the $n$-color
partitions of $r$ into an odd (resp. even) number of distinct colored parts, and let
$C_{e-o}(r) = \sum_\lambda (-1)^{\ell(\lambda)}$, the sum running over all $n$-color partitions
$\lambda$ of $r$, where $\ell(\lambda)$ is the number of parts of $\lambda$ counted with
multiplicity. Then for every $m \ge 1$,

$$\sigma_{\mathrm{odd}}(m) =
\sum_{k=1}^{m} \bigl(C_o(D, k) + C_e(D, k)\bigr)\, C_{e-o}(m-k),$$

where $\sigma_{\mathrm{odd}}(m)$ is the sum of the odd divisors of $m$.

This is the reading given by the paper's derivation from Theorem 8 and Eq. (3). As printed,
with the number $C(D, k)$ of $n$-color partitions of $k$ into distinct colored parts in place
of $C_o(D, k) + C_e(D, k)$, it fails at $m = 3$: $\sigma_{\mathrm{odd}}(3) = 4$, but
$\sum_{k=1}^{3} C(D, k)\, C_{e-o}(3-k) = 1 \cdot (-1) + 2 \cdot (-1) + 5 \cdot 1 = 2$.

## Sources

- Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*, INTEGERS 25 (2025), Article A94, Corollary 9 (`integers-2025-A94-cor-9`).
