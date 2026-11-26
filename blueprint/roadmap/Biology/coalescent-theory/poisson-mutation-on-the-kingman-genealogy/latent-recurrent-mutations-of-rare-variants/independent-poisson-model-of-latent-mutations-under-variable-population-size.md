# Independent-Poisson model of latent mutations under variable population size

Let a large sample have a gene genealogy from a general coalescent tree (Kingman branching structure with arbitrary distribution of the coalescence intervals $T_k$, the time during which there are $k$ ancestral lineages), and let $\tau_i$ be the total length of branches with exactly $i$ descendants in the sample, with mean

$$\bar\tau_i = \mathbb{E}[\tau_i] = \sum_{k=2}^{n} k\,\mathbb{E}[T_k]\,\frac{\binom{n-i-1}{k-2}}{\binom{n-1}{k-1}}$$

(so $\bar\tau_i = 2/i$ for the standard constant-size coalescent). Mutations to a variant of interest arise at rate $\theta/2$ per unit branch length (with $\theta$ standing for $\theta\pi_1$). Let $a_i$ be the number of latent mutations of the variant that have exactly $i$ copies in the sample.

**Model.** As the total sample size tends to infinity with the largest rare count $b$ fixed, $(a_1, \dots, a_b)$ converge to independent Poisson variables with means $\theta\bar\tau_i/2$, provided the genealogy has finite total height. Hence the variant's sample count $n_1 = \sum_i i\,a_i$ and its number of latent mutations $k_1 = \sum_i a_i$ satisfy

$$P(k_1) \approx \frac{\Lambda^{k_1}}{k_1!}e^{-\Lambda}, \qquad \Lambda = \frac{\theta}{2}\sum_{i=1}^{n-1}\bar\tau_i,$$

and, conditional on $k_1 \ge 1$,

$$P(n_1 \mid k_1) \approx \sum_{\substack{i_1 + \dots + i_{k_1} = n_1 \\ i_m \ge 1}} \prod_{m=1}^{k_1}\frac{\bar\tau_{i_m}}{\sum_{i=1}^{n-1}\bar\tau_i},$$

the sum running over ordered compositions of $n_1$. Thus, given $k_1$, the count $n_1$ is the sum of $k_1$ independent mutation sizes, each equal to $i$ with probability $\bar\tau_i/\sum_j\bar\tau_j$; it depends on the relative expected branch lengths but not on $\theta$. Fast-mutating sites therefore show fewer rare variants and more intermediate ones than the infinite-sites spectrum predicts, by an amount computable from the slow-site spectrum.

## Depends on

- [Ewens distribution of latent mutations of a rare variant](ewens-distribution-of-latent-mutations-of-a-rare-variant.md)
- [Total branch length subtending $i$ sample copies](../../expected-site-frequency-spectrum/sfs-length.md)
- [Expected SFS under a variable population size](../../site-frequency-spectrum-under-variable-populatio/integral-sfs-of-indep.md)
- [Infinite-sites mutation on a finite genealogy](../branch-mutation-kernel.md)

## Proof depends on

- [Ewens sampling formula](../../../population-genetics/ewens-sampling-formula-and-the-chinese-restauran/ewens-prob.md)

## Expansion

Independence of the low-count classes is equivalent to latent mutations of a rare variant not being nested, which holds in the large-sample limit because branches with few descendants are short and occur at the tips. The probability generating function factorizes, $\mathbb{E}[x^{n_1}y^{k_1}] = e^{-\Lambda}\sum_k \frac{(\theta y/2)^k}{k!}\big(\sum_i x^i\bar\tau_i\big)^k$, and extracting the coefficient of $x^{n_1}y^{k_1}$ gives $P(n_1, k_1) = e^{-\Lambda}\frac{(\theta/2)^{k_1}}{k_1!}\sum\prod_m\bar\tau_{i_m}$ over ordered compositions; dividing by the Poisson law of $k_1$ cancels the $1/k_1!$ and gives the conditional law. For the constant-size coalescent, $\bar\tau_i = 2/i$ and the counts $a_i$ are Poisson with means $\theta/i$, which by Watterson's theorem (conditioning independent Poissons on $\sum_i i a_i$) reproduces the Ewens distribution of the previous article in the large-sample limit (Eqs. (26)–(31) of the source, which also derives exponential-growth spectra and applies the model to human synonymous variants binned by mutation rate).

## Sources

- J. Wakeley, W. Fan, E. Koch, S. Sunyaev, "Recurrent mutation in the ancestry of a rare variant", Genetics (2023), <https://doi.org/10.1093/genetics/iyad049> (PMC10324944).
