# Skygrid multilocus coalescent model

**Data and grid.** Let $\mathbf g = (g_1, \dots, g_J)$ be genealogies of $J$ unlinked loci sampled from one population with effective population size trajectory $N_e(t)$, $t$ measured backward from the most recent sample. Fix a cutoff $T > 0$ and $M$ grid points $0 < x_1 < \dots < x_M = T$ (equally spaced in the basic form). The effective population size is piecewise constant, changing only at grid points:

$$N_e(t) = e^{\gamma_k} \ \text{ for } t \in (x_{k-1}, x_k], \quad k = 1, \dots, M, \qquad N_e(t) = e^{\gamma_{M+1}} \ \text{ for } t > x_M,$$

with $x_0 = 0$ and log-sizes $\boldsymbol\gamma = (\gamma_1, \dots, \gamma_{M+1})$.

**Likelihood.** Split each genealogy at grid points and at its sampling and coalescent times into intervals on which $N_e$ and the number $n$ of lineages are constant. By the variable-population coalescent of Griffiths and Tavaré, an interval of length $\Delta$ with $n$ lineages, ending in a coalescence ($\delta = 1$) or not ($\delta = 0$), contributes

$$\Bigl(\frac{\binom n2}{N_e}\Bigr)^{\delta} \exp\Bigl(-\binom n2 \frac{\Delta}{N_e}\Bigr),$$

and the likelihood of $\mathbf g$ is the product over intervals and over loci, the loci being conditionally independent given $\boldsymbol\gamma$. Grouping by grid cell, the log-likelihood is $\sum_{k} \bigl(-c_k \gamma_k - \beta_k e^{-\gamma_k}\bigr)$ up to constants, where $c_k$ counts coalescences in cell $k$ over all loci and $\beta_k \ge 0$ sums $\binom n2 \Delta$ over the corresponding intervals.

**Prior.** A first-order Gaussian Markov random field on $\boldsymbol\gamma$ with precision $\tau$,

$$p(\boldsymbol\gamma \mid \tau) \propto \tau^{M/2} \exp\Bigl(-\frac\tau2 \sum_{k=1}^{M} (\gamma_{k+1} - \gamma_k)^2\Bigr) = \tau^{M/2}\exp\Bigl(-\frac\tau2\, \boldsymbol\gamma^\top Q \boldsymbol\gamma\Bigr),$$

with $Q$ the tridiagonal random-walk structure matrix, and a gamma prior on $\tau$ (shape and rate $0.001$ in the source examples, prior mean $1$ and variance $1000$). The posterior of $(\boldsymbol\gamma, \tau)$ given $\mathbf g$ is proportional to the product of the multilocus likelihood and these priors; jointly with sequence data, the genealogies are latent and the coalescent acts as their prior.

The prior is improper in the overall level of $\boldsymbol\gamma$ ($Q\mathbf 1 = 0$): it controls the smoothness of the trajectory, not its height. The log-likelihood is concave in each $\gamma_k$ (second derivative $-\beta_k e^{-\gamma_k} \le 0$), which underlies the Gaussian (Newton–Raphson) proposals used for block updates.

## Expansion

The interval factor is the density (or survival probability) of an exponential waiting time with rate $\binom n2/N_e$. Writing $N_e = e^{\gamma_k}$ turns each factor into $\exp(-\delta\gamma_k - \binom n2 \Delta e^{-\gamma_k})$ up to the constant $\binom n2^{\delta}$, which is linear plus convex in $-\gamma_k$; products over loci simply add the counts $c_k$ and exposures $\beta_k$.

## Sources

- M. S. Gill, P. Lemey, N. R. Faria, A. Rambaut, B. Shapiro and M. A. Suchard, *Improving Bayesian population dynamics inference: a coalescent-based model for multiple loci*, Mol. Biol. Evol. 30 (2013), 713–724, <https://doi.org/10.1093/molbev/mss265>, PMCID PMC3563973 (Materials and Methods: piecewise constant demographic model, equations (6)–(12); GMRF prior, equations (13)–(15); posterior, equations (16) and (24)).
- R. C. Griffiths and S. Tavaré, *Sampling theory for neutral alleles in a varying environment*, Philos. Trans. R. Soc. Lond. B 344 (1994), 403–410, <https://doi.org/10.1098/rstb.1994.0079>.
