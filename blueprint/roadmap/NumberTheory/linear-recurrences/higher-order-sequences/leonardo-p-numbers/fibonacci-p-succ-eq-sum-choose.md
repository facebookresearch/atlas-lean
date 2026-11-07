# Binomial sum formula for Fibonacci p-numbers

For all natural numbers $p \ge 1$ and $n$,
the Fibonacci $p$-numbers $F_p$ satisfy

$$F_p(n+1) = \sum_{i=0}^{\lfloor n/(p+1) \rfloor} \binom{n-ip}{i}.$$

The paper (Theorem 8, quoting Kuhapatanakul) also gives the form
$F_p(n) = \sum_{i=0}^{\lfloor (n-1)/(p+1) \rfloor} \binom{n-1-ip}{i}$, which is the same identity
with $n$ shifted by one. The paper allows all natural $p$, but at $p = 0$ the sequence is
identically zero ($F_0(1) = F_0(0) + F_0(0) = 0$) while the sum at $n = 0$ is
$\binom{0}{0} = 1$, so $p \ge 1$ is assumed.

## Sources

- Clemens Schütz and Kristian Kelly, *An Explicit Formula for Supergeneralized Leonardo `p`-numbers*, Journal of Integer Sequences 28 (2025), Article 25.8.2, Theorem 8 (Kuhapatanakul).
