# Poisson beads-on-a-string model of Hi-C contact counts

Divide a genomic region into $n$ consecutive loci of equal size and represent locus $i$ by a bead
at $\mathbf x_i \in \mathbb R^3$, so that the average spatial distance between loci $i$ and $j$ is
$d_{ij} = \|\mathbf x_i - \mathbf x_j\|$. Let $u_{ij}$ be the Hi-C count of paired-end reads joining
loci $i \ne j$, and let $e_i$, $g_i$ and $m_i$ be the number of restriction fragment ends, the mean
GC content and the mean mappability of fragment ends in locus $i$. The model assumes the
off-diagonal counts are independent with

$$u_{ij} \sim \operatorname{Poisson}(\theta_{ij}), \qquad
\log\theta_{ij} = \beta_0 + \beta_1 \log d_{ij} + \beta_{\mathrm{enz}}\log(e_i e_j)
+ \beta_{\mathrm{gcc}}\log(g_i g_j) + \beta_{\mathrm{map}}\log(m_i m_j),$$

with $\beta_1 < 0$ expressing that contact frequency falls with spatial distance. Writing
$X = (\mathbf x_1, \dots, \mathbf x_n)$ and $\beta$ for the regression coefficients, the likelihood
is

$$L(X, \beta) = \prod_{i<j} \frac{\theta_{ij}^{\,u_{ij}}\, e^{-\theta_{ij}}}{u_{ij}!},$$

and with non-informative priors the structure is inferred from the posterior
$\pi(X, \beta \mid U) \propto L(X, \beta)\,\pi(\beta)$.

**Invariances.** The likelihood depends on $X$ only through the distances, so it is unchanged by
rigid motions and reflections of $X$. It is also unchanged by rescaling: for every $c > 0$, replacing
each $\mathbf x_i$ by $c\,\mathbf x_i$ and $\beta_0$ by $\beta_0 - \beta_1 \log c$ leaves every
$\theta_{ij}$, hence $L$, unchanged, while for $c \ne 1$ it multiplies every distance by $c$. So
$L(X, \beta) = L(cQX + \mathbf t, \beta')$ for every orthogonal $Q$, translation $\mathbf t$ and
$c > 0$, with $\beta'$ equal to $\beta$ except $\beta'_0 = \beta_0 - \beta_1 \log c$, and the counts
can determine the configuration at most up to similarity transformations; its absolute scale has to
be fixed by information outside the model.

## Expansion

Ligation frequency in a Hi-C library reflects both proximity in the nucleus and technical biases:
loci with more restriction sites produce more ligatable ends, and GC content and mappability
affect amplification and alignment. The log link turns these multiplicative effects into additive
terms, and the power law $\theta \propto d^{\beta_1}$ converts counts into an implied distance.
Posterior sampling over the $3n$ coordinates is high-dimensional; the source initializes the
nuisance coefficients by Poisson regression, grows an initial structure by sequential importance
sampling, and refines it by a Gibbs sampler with hybrid Monte Carlo and adaptive rejection
sampling. Averaging posterior samples gives a consensus structure and its variability. For the
rescaling invariance, $\beta_0' + \beta_1 \log(c\,d_{ij}) = \beta_0 + \beta_1 \log d_{ij}$; under a
prior that is flat in $\beta_0$ the posterior inherits the same invariance. The source accordingly
calibrates the scale of its inferred structures against FISH distance measurements (Fig. S2C–D).

## Sources

- M. Hu, K. Deng, Z. Qin, J. Dixon, S. Selvaraj, J. Fang, B. Ren, J. S. Liu, "Bayesian inference
  of spatial organizations of chromosomes", PLoS Computational Biology 9 (2013) e1002893, Methods,
  "The BACH algorithm", <https://doi.org/10.1371/journal.pcbi.1002893> (PMC3561073).
