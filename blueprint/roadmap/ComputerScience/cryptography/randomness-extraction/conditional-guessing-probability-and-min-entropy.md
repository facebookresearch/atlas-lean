# Conditional guessing probability and min-entropy

Let $(s, z)$ be a pair of random variables on a finite set $S \times Z$. The worst-case conditional guessing probability is $\gamma_{\mathrm{wc}}(s \mid z) = \max_{z_0} \max_{x} \Pr[s = x \mid z = z_0]$, the maximum over $z_0$ with $\Pr[z = z_0] > 0$, and the average-case conditional guessing probability is $\gamma_{\mathrm{avg}}(s \mid z) = \sum_{z_0} \max_x \Pr[s = x, z = z_0]$. The corresponding conditional min-entropies are $-\log_2 \gamma_{\mathrm{wc}}$ and $-\log_2 \gamma_{\mathrm{avg}}$, and $\gamma_{\mathrm{avg}}(s \mid z) \le \gamma_{\mathrm{wc}}(s \mid z)$.

## Depends on

- [Guessing probability, min-entropy and collision probability](guessing-probability-min-entropy-and-collision.md)

## Sources

- Y. Dodis, R. Ostrovsky, L. Reyzin and A. Smith, "Fuzzy extractors: how to generate strong keys from biometrics and other noisy data", *SIAM Journal on Computing* 38(1):97–139, 2008
