# MAPS Poisson composite likelihood for migration and population-size surfaces

Let $n$ haploid individuals be sampled from demes of a triangular grid of $d$ demes with symmetric migration rates $M$ and coalescence rates $q = (q_\kappa)$, $\Theta = (M, q)$. For a length range $R$, let $X^R_{ij}$ be the number of [pairwise shared coalescence segments](expected-number-of-long-shared-coalescence-segments-in-a-stepping-stone-model.md) with length in $R$ shared by $i$ and $j$, and for individuals sampled in demes $\alpha, \beta$ put $\lambda^{\Theta}_{\alpha\beta} = \mathbb{E}[X^R_{ij} \mid \Theta]$.

**Composite likelihood.** Model each count as $X^R_{ij} \mid \Theta \sim \mathrm{Pois}(\lambda^\Theta_{\alpha\beta})$. Let $n_\alpha$ be the number of samples in deme $\alpha$, $n_{\alpha\beta} = n_\alpha n_\beta$ for $\alpha \ne \beta$ and $n_{\alpha\alpha} = \binom{n_\alpha}{2}$, and $\bar X_{\alpha\beta}$ the average of $X^R_{ij}$ over these pairs. Treating pairs as independent gives $\sum_{\alpha \le \beta} n_{\alpha\beta}\big(\bar X_{\alpha\beta}\log\lambda^\Theta_{\alpha\beta} - \lambda^\Theta_{\alpha\beta}\big)$. Because counts are positively correlated across pairs sharing an individual, MAPS replaces $n_{\alpha\beta}$ by the **effective number of samples**

$$e_{\alpha\beta} = \frac{\bar X_{\alpha\beta}}{\widehat{\operatorname{Var}}[\bar X_{\alpha\beta}]},$$

with the variance estimated by bootstrapping individuals within demes, and uses

$$\log L(\Theta; \bar X) = \sum_{\alpha \le \beta} e_{\alpha\beta}\big(\bar X_{\alpha\beta}\log\lambda^\Theta_{\alpha\beta} - \lambda^\Theta_{\alpha\beta}\big).$$

Under independence $\operatorname{Var}[\bar X_{\alpha\beta}] \approx \bar X_{\alpha\beta}/n_{\alpha\beta}$ and $e_{\alpha\beta} = n_{\alpha\beta}$, recovering the naive likelihood.

**Prior and continuous-space parameters.** Migration rates and population sizes are given piecewise-constant hierarchical priors over separate Voronoi tessellations of the habitat (one for each): demes in cell $c$ get $N_\alpha = N_c$, and the edge between demes in cells $c_1, c_2$ gets $m_{\alpha\beta} = (M_{c_1} + M_{c_2})/2$. The posterior is sampled by Metropolis–Hastings MCMC with birth–death moves on the number of cells. Grid parameters are converted to continuous-space quantities: with habitat area $A_H$ and $\Delta A = A_H/d$ the area per deme, the **effective population density** is $D_e(x) = N_\alpha/\Delta A$ at the position $x$ of deme $\alpha$, and with grid step $\Delta x$ a migration rate $m$ corresponds to the **root-mean-square dispersal distance** $\sigma = \sqrt{m}\,\Delta x$ per generation.

## Remarks

For independent Poisson counts with common mean $\lambda$, the log-likelihood of $n_{\alpha\beta}$ pairs depends on the data only through $\bar X_{\alpha\beta}$ and equals $n_{\alpha\beta}(\bar X_{\alpha\beta}\log\lambda - \lambda)$ up to a constant. A Poisson sample of size $e$ has $\operatorname{Var}(\bar X) = \lambda/e$; matching this to the observed (bootstrap) variance of the average with $\lambda \approx \bar X$ defines $e_{\alpha\beta}$, so the weighting tempers the likelihood to the information actually present when pairs overlap. The dispersal conversion follows from matching the variance of displacement per generation: on a grid with step $\Delta x$, a lineage jumping to a neighbouring deme at rate $m$ per generation has displacement variance proportional to $m\,\Delta x^2$, whose square root is the dispersal scale; the density conversion simply equates $D_e\,\Delta A$ with $N_\alpha$. Inference on segments in different length bins (for example $2$–$8$ cM versus $\ge 8$ cM) targets different recent time scales.

## Depends on

- [Expected number of long shared-coalescence segments in a stepping-stone model](expected-number-of-long-shared-coalescence-segments-in-a-stepping-stone-model.md)

## Sources

- H. Al-Asadi, D. Petkova, M. Stephens and J. Novembre, "Estimating recent migration and population-size surfaces", *PLoS Genetics* 15 (2019), e1007908, Methods "The likelihood function", "The prior" and "Transformation of parameters to continuous space", Equations (1)–(7), (17) and (18), <https://doi.org/10.1371/journal.pgen.1007908> (PMC6347299).
