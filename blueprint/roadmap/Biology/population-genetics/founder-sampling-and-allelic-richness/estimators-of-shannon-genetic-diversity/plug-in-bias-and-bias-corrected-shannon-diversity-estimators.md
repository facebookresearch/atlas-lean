# Plug-in bias and bias-corrected Shannon diversity estimators

**Setting.** A locus has alleles $1,\dots,S$ with population frequencies $p_1,\dots,p_S > 0$ and Shannon diversity $H = -\sum_{i=1}^S p_i \log p_i$. A sample of $n$ allele copies drawn i.i.d. from $(p_i)$ gives counts $X_i$ and sample frequencies $\hat p_i = X_i / n$; let $f_1$ be the number of alleles observed exactly once (singletons).

**Plug-in (maximum-likelihood) estimator.** $\hat H_{\mathrm{MLE}} = -\sum_{i:\,X_i>0} \hat p_i \log \hat p_i$. Since $x \mapsto -x\log x$ is strictly concave, Jensen's inequality gives $\mathbb E[\hat H_{\mathrm{MLE}}] \le H$, and for fixed $S$ as $n \to \infty$

$$\mathbb E[\hat H_{\mathrm{MLE}}] = H - \frac{S - 1}{2n} + O(n^{-2}),$$

so the downward bias is largest for small samples and many alleles.

**Coverage-adjusted (Chao–Shen) estimator.** With the Good–Turing sample coverage $\hat C = 1 - f_1/n$ and $\tilde p_i = \hat C\, \hat p_i$,

$$\hat H_{\mathrm{CS}} = -\sum_{i:\,X_i>0} \frac{\tilde p_i \log \tilde p_i}{1 - (1 - \tilde p_i)^n},$$

a Horvitz–Thompson correction in which $1 - (1-\tilde p_i)^n$ is the probability that allele $i$ appears in the sample. (It is undefined when every observed allele is a singleton, since then $\hat C = 0$.)

**Jackknife (Zahl) estimator.** With $\hat H_{(-j)}$ the plug-in estimate after deleting the $j$-th sampled copy,

$$\hat H_{Z} = n\,\hat H_{\mathrm{MLE}} - \frac{n-1}{n}\sum_{j=1}^n \hat H_{(-j)},$$

which removes the $O(1/n)$ term of the bias.

## Depends on

- [Shannon entropy of a distribution](../../../../Chemistry/chemical-thermodynamics/canonical-ensemble-of-a-finite-system/shannon-entropy.md)

## Proof depends on

- [Jensen's inequality](../../../../MeasureTheory/integration/jensen-s-inequality-for-integrals/jensen-s-inequality/jensen-inequality.md)

## Expansion

The bias expansion follows from a second-order Taylor expansion of $-x \log x$ around $p_i$, using $\operatorname{Var}(\hat p_i) = p_i(1-p_i)/n$: the second derivative $-1/p_i$ contributes $-\tfrac{1}{2n}\sum_i (1 - p_i) = -\tfrac{S-1}{2n}$. The Chao–Shen correction addresses two effects at once: $\hat C$ shrinks observed frequencies to leave mass for unseen alleles, and dividing by the inclusion probability up-weights rare observed alleles. The jackknife combination $n\hat\theta - (n-1)\bar\theta_{(\cdot)}$ cancels any bias of the form $a/n + O(n^{-2})$.

## Simulation results

**Empirical comparison.** On coalescent-simulated microsatellite samples of $5$ to $200$ diploid genotypes, all estimators depended on sample size, but $\hat H_{\mathrm{MLE}}$ showed the strongest negative relative bias; the jackknife and the Chao–Wang–Jost estimator were the least biased, $\hat H_{\mathrm{CS}}$ failed to evaluate in about $10\%$ of the smallest, most variable samples, and error decreased with population heterozygosity.

## Sources

- M. K. Konopiński, "Shannon diversity index: a call to replace the original Shannon's formula with unbiased estimator in the population genetics studies", PeerJ 8:e9391 (2020), Methods (the four estimators $H_{\mathrm{MLE}}$, $H_Z$, $H_{\mathrm{CS}}$, $H_{\mathrm{Chao}}$) and Results (Tables 3–4, Fig 2), <https://doi.org/10.7717/peerj.9391>, PMCID PMC7331625.
- A. Chao, T.-J. Shen, "Nonparametric estimation of Shannon's index of diversity when there are unseen species in sample", Environmental and Ecological Statistics 10:429–443 (2003), <https://doi.org/10.1023/A:1026096204727>.
