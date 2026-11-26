# Holenstein's conditioning lemma with side information

Let $T, V$ and $\beta_1, \dots, \beta_k$ be finite sets, $\mu$ a distribution on $T$, and for each $t$ let $J_t$ be a distribution on $(\prod_j \beta_j) \times V$ whose first marginal is the product $\bigotimes_j K_j(t)$ of distributions $K_j(t)$ on $\beta_j$. Draw $t \sim \mu$ and $(u, v) \sim J_t$, and let $W$ be an event about $(t, v, u)$ with $\Pr[W] > 0$. Then

$$
\sum_{j=1}^{k} \delta\Big(P_{(T, V, U_j) \mid W},\ P_{(T,V)\mid W} \otimes K_j(T)\Big) \le \sqrt{\frac{k}{2}\ln\frac{|V|}{\Pr[W]}},
$$

where $P_{(T,V)\mid W}\otimes K_j(T)$ draws $(t, v)$ from its conditional law given $W$ and then $u_j \sim K_j(t)$ afresh. Also, if $(u, v)$ is drawn from a joint law whose $u$-marginal is $\bigotimes_j p_j$, then $\sum_j \delta(P_{U_j\mid W}, p_j)^2 \le \frac12\ln(1/\Pr[W])$.

## Proof sketch

For the second claim, the conditioned $u$-marginal has masses at most $\Pr[W]^{-1}$ times those of the product, so its divergence from the product is at most $\ln(1/\Pr[W])$ and Raz's argument applies. For the main claim, reveal $(t, v)$: each squared distance is at most the average conditional squared distance, and given $(t, v)$ the law of $u$ is $J_t$'s $u$-marginal conditioned on the slice of $W$, to which the second claim applies. Averaging the slice bounds with $\ln x \le x - 1$ costs the factor $|V|$, and Cauchy-Schwarz sums over $j$.

## Depends on

- [Raz's conditioning lemma for product distributions](raz-conditioning-lemma.md)

## Proof depends on

- [Raz's conditioning lemma for product distributions](raz-conditioning-lemma.md)

## Sources

- T. Holenstein, "Parallel Repetition: Simplifications and the No-Signaling Case", Theory of Computing 5, 2009.
