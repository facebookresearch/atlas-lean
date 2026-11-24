# Variance of the number of segregating sites with intragenic recombination

Take two samples on a chromosome $[0, 1)$ with homogeneous recombination of total rate $R = \rho \ge 0$ and mutation rate $\theta$ for the whole chromosome, and let $T_x$ be the coalescence time at position $x$. By [the conditional Poisson process of mutations](conditional-mutation-ppp-on-the-measurable-tree.md), the number $S$ of segregating sites is a mixed Poisson variable,

$$S \mid \text{graph} \sim \operatorname{Poisson}\Bigl(\theta \int_0^1 T_x\, dx\Bigr),$$

so $\mathbb{E}[S] = \theta$ and

$$\operatorname{Var}(S) = \theta + \theta^2 \int_0^1 \int_0^1 \operatorname{Cov}(T_x, T_y)\, dx\, dy.$$

For $R > 0$, the [covariance of the coalescence times at two loci](../two-locus-coalescent/covariance-coalescence-times.md) separated by recombination rate $r$ is $f(r) = (r + 18)/(r^2 + 13 r + 18)$, and

$$\operatorname{Var}(S) = \theta + \frac{2\theta^2}{R^2} \int_0^R (R - r) f(r)\, dr.$$

For $R = 0$, $T_x = T \sim \operatorname{Exp}(1)$ for all $x$ and $\operatorname{Var}(S) = \theta + \theta^2$, which is also the limit as $R \to 0$. As $R \to \infty$, $\operatorname{Var}(S) \to \theta$.

## Depends on

- [Covariance of the coalescence times, path form](../two-locus-coalescent/covariance-coalescence-times.md)
- [Continuum ARG (homogeneous recombination): finite-locus marginals and two-point law](../two-locus-coalescent/continuum-arg-homogeneous-rho-dx-finite-locus-ma.md)
- [Conditional Poisson process of mutations on the local trees](conditional-mutation-ppp-on-the-measurable-tree.md)

## Proof depends on

- [The number of segregating sites is conditionally Poisson](has-cond-distrib-seg-sites-of-mutation.md)

## Expansion

1. The mixed Poisson law, stated as a law and not only through its moments.
2. The variance formula, by the law of total variance and Fubini's theorem, justified by the joint measurability of $(x, \omega) \mapsto T_x$ from [the finiteness of the breakpoints](../pairwise-differences-under-poisson-mutation/finitely-many-breakpoints-and-a-jointly-measurab.md) and $\mathbb{E} \int_0^1 T_x^2\, dx < \infty$.
3. The closed form, from the two-point law of the continuum graph, which gives $\operatorname{Cov}(T_x, T_y) = f(R\lvert x - y\rvert)$, and the change of variables $r = R\lvert x - y \rvert$.
4. The case $R = 0$ stated separately, and the limits $R \to 0$ and $R \to \infty$.

## Sources

- R. R. Hudson, Properties of a neutral allele model with intragenic recombination, *Theor. Popul. Biol.* 23 (1983), 183–201, <https://pubmed.ncbi.nlm.nih.gov/6612631/> (variance of the number of segregating sites).
