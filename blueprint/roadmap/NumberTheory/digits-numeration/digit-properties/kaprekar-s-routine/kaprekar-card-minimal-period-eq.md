# Explicit count of Kaprekar cycles of each length

Let $B > 3$ be odd and $L \ge 1$, let
$K_B$ be the four-digit Kaprekar map and $X_B$ its state space, let $\varphi$ be Euler's totient
function, and let $\lambda(n)$ denote the projective order of $2$ modulo $n$. For $a \ge 1$ put

$$\mu_B(a) = \sum_{n \mid B,\ n > 1,\ \lambda(n) = a}
\left\lfloor \frac{\varphi(n)}{2a} \right\rfloor$$

and

$$N_B(L) = \mu_B(L) \left\lfloor \frac{L - 1}{2} \right\rfloor + \mu_B(2L) +
\binom{\mu_B(L)}{2} L + \sum_{a, b \mid L,\ a < b,\ \operatorname{lcm}(a, b) = L}
\mu_B(a)\, \mu_B(b) \gcd(a, b),$$

where $n$ ranges over positive divisors of $B$ and $a, b$ in the last sum range over positive
divisors of $L$. Then exactly $L \cdot N_B(L)$ points of $X_B$ have minimal period $L$ under
$K_B$.

Here $N_B(L)$ is the number of terminal cycles of length $L$ of $K_B$ on $X_B$.

## Sources

- Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7, Theorem 24, with `μ_B` from display (14) (`jis-2026-26.4.7-thm-24`).
