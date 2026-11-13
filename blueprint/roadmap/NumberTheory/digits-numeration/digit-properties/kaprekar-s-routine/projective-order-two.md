# Projective order of 2

For a natural number $n$, the projective order of $2$ modulo $n$ is
the least $m > 0$ with $2^m \equiv 1$ or $2^m \equiv -1 \pmod{n}$,

$$\lambda(n) = \min \{m > 0 : 2^m \equiv \pm 1 \pmod{n}\},$$

and $\lambda(n) = 0$ when no such $m$ exists, which happens exactly when $n$ is even (including
$n = 0$, where congruence modulo $0$ is equality of integers). For odd $n$ these are the terms of
OEIS A003558, which lists $\lambda(2k + 1)$ at index $k$.

## Sources

- Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7, Definition 19, display (13).
