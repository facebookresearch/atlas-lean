# Product formulas for the sum of squared divisors

Let $n \ne 0$ be a natural number,
let $\sigma_2(n)$ be the sum of the squares of the divisors of $n$, and for each prime $p$
dividing $n$ let $k_p$ be the exponent of $p$ in $n$. Then, with products over the primes $p$
dividing $n$,

$$\sigma_2(n) = \prod_{p \mid n} \frac{p^{2(k_p + 1)} - 1}{p^2 - 1}$$

and

$$\frac{\sigma_2(n)}{n^2} = \prod_{p \mid n} \frac{p^{2(k_p + 1)} - 1}{p^{2k_p} (p^2 - 1)}.$$

If moreover $n > 1$, then $\sigma_2(n)/n^2 < \prod_{p \mid n} p^2/(p^2 - 1)$.

## Sources

- Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller Numbers*, INTEGERS 24 (2024), Article A95, Lemma 1(ii) (quoting Peng and Bhaskara Rao).
