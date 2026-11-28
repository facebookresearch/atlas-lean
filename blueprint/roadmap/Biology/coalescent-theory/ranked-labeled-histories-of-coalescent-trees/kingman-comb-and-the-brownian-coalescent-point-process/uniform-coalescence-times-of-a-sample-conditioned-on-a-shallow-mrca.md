# Uniform coalescence times of a sample conditioned on a shallow common ancestor

Let $n \ge 2$ and consider Kingman's coalescent, the genealogy of $n$ individuals sampled from a large neutral population of constant size (the stationary Fleming–Viot process). Condition the sample to have its most recent common ancestor (MRCA) at depth less than $\varepsilon$, and rescale depths by $\varepsilon^{-1}$. This can be done in two ways.

- *Averaged conditioning.* Let $T_n < T_{n-1} < \dots < T_2$ be the successive coalescence times of the $n$-Kingman coalescent, so $T_2$ is the MRCA depth. Define $(T^\varepsilon_i)_{i=2}^n$ to be $(\varepsilon^{-1}T_i)_{i=2}^n$ conditioned on $\{T_2 < \varepsilon\}$.
- *Quenched conditioning.* Given the realized population (the flow of bridges), sample $n$ individuals uniformly, conditioned to share an ancestor at depth $\varepsilon$, and average over populations. Ordering the sample along the population's genealogical linear order, let $H^\varepsilon_1,\dots,H^\varepsilon_{n-1}$ be the coalescence times of consecutive sampled individuals.

**Theorem.** As $\varepsilon \to 0$:

1. *(Quenched.)* $(\varepsilon^{-1}H^\varepsilon_i)_{i=1}^{n-1}$ converges in distribution to $n-1$ i.i.d. uniform variables on $(0,1)$.
2. *(Averaged.)* The ranked times $(T^\varepsilon_i)_{i=2}^n$ converge in distribution to the order statistics of $n-1$ i.i.d. uniform variables on $(0,1)$.

In particular, the two conditionings give the same limiting sample genealogy. In both, the rescaled node depths of the sample tree are i.i.d. uniform, as in a coalescent point process with uniform node depths.

## Expansion

*Quenched case.* By the [Brownian CPP limit under conditional sampling](brownian-cpp-limit-of-the-kingman-comb-under-conditional-sampling.md), the rescaled family of the sample converges to a CPP $\mathcal{M}_\infty$ with intensity $2y^{-2}dy\,\mathbf{1}_{\{y<1\}}$, killed at an independent $\mathcal{L}_n \sim \mathrm{Gamma}(n+1,2)$. Given the family size, the $n$ sampled positions are uniform on it. Size-biasing by $\mathcal{L}_n^n$ exactly cancels the uniform-placement density, so the $n-1$ spacings between consecutive sampled positions are i.i.d. $\mathrm{Exp}(2)$. A spacing of length $x$ has no CPP atom above $\sigma$ with probability $\exp(-2x(\sigma^{-1}-1))$. Integrating against $2e^{-2x}dx$ gives $\sigma$, so each consecutive coalescence time is uniform on $(0,1)$, independently (Lemma 5.3). A truncation and uniform-integrability argument justifies passing to the limit (Lemma 5.2).

*Averaged case.* As $\varepsilon \to 0$, the joint density of the $n-1$ exponential inter-coalescence times is asymptotically constant on the region $\{T_2 < \varepsilon\}$. So the conditioned, rescaled coalescence times become uniform on the simplex $\{0 < t_n < \dots < t_2 < 1\}$, which is the law of uniform order statistics.

## Depends on

- [Brownian CPP limit of the Kingman comb under quenched conditional sampling](brownian-cpp-limit-of-the-kingman-comb-under-conditional-sampling.md)

## Sources

- Amaury Lambert and Emmanuel Schertzer, "Recovering the Brownian coalescent point process from the Kingman coalescent by conditional sampling", *Bernoulli* 25(1) (2019), 148–173. <https://doi.org/10.3150/17-BEJ971>
- Preprint version (the locators in this item follow its numbering): A. Lambert and E. Schertzer, "Recovering the Brownian Coalescent Point Process from the Kingman Coalescent by Conditional Sampling", arXiv:1611.01323 (2016), <https://doi.org/10.48550/arXiv.1611.01323>. Theorem 5.1 (quenched conditional sampling), Lemmas 5.2–5.3, Theorem 5.4 (averaged conditional sampling).
