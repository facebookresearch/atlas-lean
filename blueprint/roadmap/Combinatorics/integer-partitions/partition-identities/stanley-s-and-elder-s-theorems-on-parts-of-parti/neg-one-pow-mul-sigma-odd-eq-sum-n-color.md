# Signed odd-divisor sum via $n$-color partitions into odd parts

For $r \ge 0$ let
$U_o(r)$ (resp. $U_e(r)$) be the total number of parts, counted with multiplicity, over the
$n$-color partitions of $r$ in which every part has odd size and the number of parts is odd
(resp. even), and let $C(O, D, r)$ be the number of $n$-color partitions of $r$ into distinct
colored parts all of odd size. Then for every $m \ge 1$,

$$(-1)^{m+1} \sigma_{\mathrm{odd}}(m) =
\sum_{k=1}^{m} \bigl(U_o(k) - U_e(k)\bigr)\, C(O, D, m-k),$$

where $\sigma_{\mathrm{odd}}(m)$ is the sum of the odd divisors of $m$.

The subscripts of $U_o$ and $U_e$ give the parity of the number of parts. With the printed
(swapped) definition of $U_o$ and $U_e$ the identity fails at $m = 1$: the left side is $1$
and the right side is $(0 - 1) \cdot 1 = -1$.

## Sources

- Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*, INTEGERS 25 (2025), Article A94, Corollary 13 (`integers-2025-A94-cor-13`).
