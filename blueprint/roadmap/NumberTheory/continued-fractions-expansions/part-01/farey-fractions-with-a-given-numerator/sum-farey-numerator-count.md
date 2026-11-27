# Farey fractions with numerator at most a given bound

Let $m$ and $n$ be natural numbers with $0 < m < n$, let $N_n(h)$ denotes the number of fractions of the Farey sequence of order $n$ with numerator $h$, that is, of denominators $b$ with $h \le b \le n$ and $\gcd(h, b) = 1$, and let $\{n/d\} = (n \bmod d)/d$ denotes the fractional part. Then

$$\sum_{h=1}^{m} N_n(h) = 1 + n \sum_{h=1}^{m} \frac{\varphi(h)}{h} - \sum_{h=1}^{m} \varphi(h) - \sum_{h=1}^{m} \sum_{d \mid h} \mu(d) \left\{\frac{n}{d}\right\},$$

where $\varphi$ is Euler's totient function and $\mu$ the Möbius function.

## Sources

Rogelio Tomás García, "Farey Fractions with Equal Numerators and the Rank of Unit Fractions", INTEGERS 24 (2024), Article A63, Corollary 4.
