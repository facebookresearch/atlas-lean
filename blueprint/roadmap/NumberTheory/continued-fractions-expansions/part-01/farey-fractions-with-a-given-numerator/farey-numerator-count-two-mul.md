# Farey fractions with numerator twice a given number

Let $h$ and $n$ be natural numbers with $0 < h$ and $2h < n$, let $N_n(h)$ denotes the number of fractions of the Farey sequence of order $n$ with numerator $h$, that is, of denominators $b$ with $h \le b \le n$ and $\gcd(h, b) = 1$, $\varphi$ Euler's totient function and $\mu$ the Möbius function. Then:

1. if $h$ is even, $N_n(2h) = N_n(h) - \varphi(h)$;
2. if $h$ is odd, $2 N_n(2h) = N_n(h) - \varphi(h) - \delta_{1h} + \sum_{d \mid h} \mu(d) \left(\lfloor n/d \rfloor \bmod 2\right)$, where $\delta_{1h}$ is $1$ for $h = 1$ and $0$ otherwise.

## Sources

Rogelio Tomás García, "Farey Fractions with Equal Numerators and the Rank of Unit Fractions", INTEGERS 24 (2024), Article A63, Corollary 3.
