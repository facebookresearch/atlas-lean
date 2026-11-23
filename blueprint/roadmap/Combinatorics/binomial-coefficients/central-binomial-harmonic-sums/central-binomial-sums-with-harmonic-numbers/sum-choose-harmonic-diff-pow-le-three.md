# Power sums of $\binom{t}{k}(H_t - H_{t-k})$ for exponents up to three

Let $n$ be a
natural number and $t$ a complex number that is not an integer. For complex $x$ write
$\binom{x}{k} = x(x-1)\cdots(x-k+1)/k!$, and write $H_x = \psi(x+1) + \gamma$, where $\psi$ is
the digamma function and $\gamma$ is the Euler–Mascheroni constant (only differences
$H_x - H_y = \psi(x+1) - \psi(y+1)$ occur below). For natural $r$ let
$L_r = \sum_{k=0}^{n} (-1)^k k^r \binom{t}{k} (H_t - H_{t-k})$ (with $0^0 = 1$), and for natural
$j$ let $A_j = \binom{n-t}{n-j} (H_{j-t} - H_{n-t})$ if $j \le n$ and $A_j = 0$ if $j > n$. Then
$L_0 = A_0$, $L_1 = -A_1 + n A_0$, $L_2 = 2 A_2 - (2n-1) A_1 + n^2 A_0$ and
$L_3 = -6 A_3 + 6(n-1) A_2 - (3n^2 - 3n + 1) A_1 + n^3 A_0$.

These are the cases $r = 0, 1, 2, 3$ of the paper's Theorem 4.

## Sources

- Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109, Proposition 1.
