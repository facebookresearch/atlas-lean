# Rank of two over an odd number in a Farey sequence

Let $k$ and $n$ be natural numbers with $k$ odd and $2 < k \le n$, let $q = \lfloor 2n/k \rfloor$, and let $\{n/d\} = (n \bmod d)/d$ denotes the fractional part. Then

$$I_n(2/k) = n \sum_{j=1}^{q} \frac{\varphi(j)}{j} - \frac{k}{2} \sum_{j=1}^{q} \varphi(j) - \sum_{j=1}^{q} \sum_{d \mid j} \mu(d) \left\{\frac{n}{d}\right\},$$

where $I_n(x)$ counts the fractions $r$ of the Farey sequence of order $n$ with $0 < r < x$, $\varphi$ is Euler's totient function and $\mu$ the Möbius function.

## Sources

Rogelio Tomás García, "Farey Fractions with Equal Numerators and the Rank of Unit Fractions", INTEGERS 24 (2024), Article A63, Corollary 8, first part.
