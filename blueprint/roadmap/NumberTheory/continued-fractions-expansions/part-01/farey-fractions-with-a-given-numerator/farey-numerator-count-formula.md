# Formula for the number of Farey fractions with a given numerator

Let $h$ and $n$ be
natural numbers with $0 < h < n$, and let $N_n(h)$ be the number of integers $b$ with
$h \le b \le n$ and $\gcd(h, b) = 1$ (the number of fractions with numerator $h$ in the Farey
sequence of order $n$). Then

$$
N_n(h) = \frac{n \varphi(h)}{h} - \sum_{d \mid h} \mu(d) \frac{n \bmod d}{d} -
\varphi(h) + \delta_{1h},
$$

where $\varphi$ is Euler's totient function, $\mu$ is the Möbius function, the sum runs over the
positive divisors $d$ of $h$, $(n \bmod d)/d$ is the fractional part of $n/d$, and $\delta_{1h}$ is
$1$ if $h = 1$ and $0$ otherwise.

## Sources

- Rogelio Tomás García, "Farey Fractions with Equal Numerators and the Rank of Unit Fractions", Theorem 1.
