# Product formulas for the sum of divisors

Let $n \ne 0$ be a natural number, let
$\sigma(n)$ be the sum of the divisors of $n$, and for each prime $p$ dividing $n$ let $k_p$ be
the exponent of $p$ in $n$. Then, with products over the primes $p$ dividing $n$,

$$\sigma(n) = \prod_{p \mid n} \frac{p^{k_p + 1} - 1}{p - 1}$$

and

$$\frac{\sigma(n)}{n} = \prod_{p \mid n} \frac{p^{k_p + 1} - 1}{p^{k_p} (p - 1)}.$$

If moreover $n > 1$, then $\sigma(n)/n < \prod_{p \mid n} p/(p - 1)$.

## Sources

- Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller Numbers*, INTEGERS 24 (2024), Article A95, Lemma 1(i) (quoting Peng and Bhaskara Rao).
