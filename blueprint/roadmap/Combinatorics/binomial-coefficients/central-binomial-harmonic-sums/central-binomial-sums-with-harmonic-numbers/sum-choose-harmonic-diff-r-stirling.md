# Power sums of $\binom{t}{k}(H_t - H_{t-k})$ in r-Stirling form

Let $t$ be a complex
number that is not an integer. For complex $x$ write $\binom{x}{k} = x(x-1)\cdots(x-k+1)/k!$,
and write $H_x = \psi(x+1) + \gamma$, where $\psi$ is the digamma function and $\gamma$ is the
Euler–Mascheroni constant (only differences $H_x - H_y = \psi(x+1) - \psi(y+1)$ occur below).
Let ${a \brace b}_c$ denote the r-Stirling numbers of the second kind. For all natural numbers
$n$ and $r$ (with $0^0 = 1$),

$$\sum_{k=0}^{n} (-1)^k k^r \binom{t}{k} (H_t - H_{t-k}) =
\sum_{k=0}^{\min(r,n)} (-1)^k k! {r+n-k \brace n}_{n-k} \binom{n-t}{n-k} (H_{k-t} - H_{n-t}).$$

## Sources

- Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109, Theorem 4 (`integers-2026-A109-thm-4`).
