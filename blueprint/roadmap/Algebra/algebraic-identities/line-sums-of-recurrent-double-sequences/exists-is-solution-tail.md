# A sequence satisfying an eventual backward recurrence has a recurrent tail

Let $x \colon \mathbb{Z} \to \mathbb{C}$, $N \in \mathbb{Z}$, $M \in \mathbb{N}$ and $D = \sum_{i=0}^{d} D_i X^i$ a complex polynomial of degree $d$ with $D(0) = D_0 \ne 0$, such that

$$\sum_{i=0}^{d} D_i\, x(N + m - i) = 0 \quad \text{for all } m \ge M.$$

Then there is a linear recurrence of order $d$ (coefficients $a_0, \dots, a_{d-1} \in \mathbb{C}$) satisfied by the tail $u_n = x(N + M + n)$, $n \in \mathbb{N}$: $u_{n+d} = \sum_{i < d} a_i u_{n+i}$ for all $n$. The order-zero case ($D$ constant, so the tail is zero) is included.
