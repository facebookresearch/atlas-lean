# Positive integer roots of the Nicomachean factor for $s = 1, 2$

Let
$\alpha(n, s, a) = 2n^2 + na - a^2 + n(n-1)(s - s^2)/2 - (n-1)as$ and let $F_0 = 0$, $F_1 = 1$,
$F_{k+2} = F_{k+1} + F_k$ be the Fibonacci numbers. Let $n \ge 1$ be a natural number. Then
$\alpha(n, 1, h) = 0$ for some positive integer $h$ if and only if $2n^2 = k(k+1)$ for some natural
number $k$, that is, $n^2$ is a triangular number; $\alpha(n, 2, h) = 0$ for some positive integer
$h$ if and only if $n = F_{2k}$ for some $k \ge 1$; and if $n = F_{2k}$ with $k \ge 1$, then every
positive integer $h$ with $\alpha(n, 2, h) = 0$ equals $F_{2k-1} + 1$.

By the factor theorem, $\alpha(n, s, h) = 0$ says that $a - h$ divides $\alpha(n, s, a)$ as a
polynomial in $a$. The case $n = 0$ is excluded: $\alpha(0, 2, a)$ has the root $2$.

## Sources

- Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 9 (`jis-2024-24.6.3-prop-9`).
