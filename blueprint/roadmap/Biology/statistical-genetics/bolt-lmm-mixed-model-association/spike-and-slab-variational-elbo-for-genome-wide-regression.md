# Spike-and-slab variational ELBO for genome-wide regression

**Model.** Let $y \in \mathbb R^N$ be a covariate-adjusted phenotype and $X \in \mathbb R^{N \times M}$ a covariate-adjusted genotype matrix. Take

$$y \mid \beta \sim \mathcal N(X\beta, \sigma_e^2 I_N), \qquad \beta_j \overset{\text{iid}}{\sim} (1 - p_0)\, \mathcal N(0, \sigma^2) + p_0\, \delta_0 ,$$

a spike-and-slab prior with spike probability $p_0 \in (0,1)$ and slab variance $\sigma^2 > 0$, and the fully factorized spike-and-slab variational family

$$q(\beta) = \prod_{j=1}^M q_j(\beta_j), \qquad q_j = \psi_j\, \delta_0 + (1 - \psi_j)\, \mathcal N(\mu_j, s_j^2),$$

with $\psi_j \in (0,1)$, $\mu_j \in \mathbb R$, $s_j > 0$.

**Proposition (KL term).** For each $j$,

$$\mathrm{KL}(q_j \,\|\, p_j) = \psi_j \log\frac{\psi_j}{p_0} + (1 - \psi_j)\log\frac{1 - \psi_j}{1 - p_0} + (1 - \psi_j)\cdot\frac12\Big(\frac{\mu_j^2 + s_j^2}{\sigma^2} - 1 - \log\frac{s_j^2}{\sigma^2}\Big),$$

the Bernoulli divergence of the spike weights plus the slab weight times the Gaussian divergence $\mathrm{KL}(\mathcal N(\mu_j, s_j^2) \,\|\, \mathcal N(0, \sigma^2))$.

**ELBO.** Consequently the evidence lower bound is

$$\mathcal L(\psi, \mu, s) = -\frac{1}{2\sigma_e^2}\, \mathbb E_q\|y - X\beta\|^2 - \frac N2 \log(2\pi\sigma_e^2) - \sum_{j=1}^M \mathrm{KL}(q_j \,\|\, p_j),$$

and splitting the samples into $B$ minibatches $(X_b, y_b)$ gives the stochastic objective

$$\mathcal L \approx -\sum_{b=1}^B \Big(\frac{1}{S}\sum_{s=1}^S \frac{\|y_b - X_b \beta^{(s)}\|^2}{2\sigma_e^2} + \frac1B \sum_{j=1}^M \mathrm{KL}(q_j \,\|\, p_j)\Big) + \text{const}, \qquad \beta^{(s)} \sim q,$$

which is maximized by stochastic gradient ascent. The fitted posterior mean gives leave-one-chromosome-out residual phenotypes for mixed-model association statistics. For binary traits the Gaussian likelihood is replaced by the logistic likelihood with the same prior and variational family.

## Depends on

- [Mean-field evidence lower bound](elbo.md)
- [Two-Gaussian mixture prior on a SNP effect](mixture-prior.md): with $v_2 = 0$

## Expansion

Both $q_j$ and $p_j$ put an atom at $0$ and a density on $\mathbb R \setminus \{0\}$, so the Radon–Nikodym derivative is $\psi_j/p_0$ on the atom and $\frac{(1-\psi_j)\,\mathcal N(\mu_j, s_j^2)}{(1-p_0)\,\mathcal N(0,\sigma^2)}$ elsewhere; integrating its logarithm against $q_j$ gives the three terms, and the KL of the factorized family is the sum over $j$. The slab weight $1 - \psi_j$ (not the spike weight) multiplies the Gaussian divergence. Compared with the infinitesimal Gaussian prior of standard mixed models, the spike lets most effects be exactly zero, which sharpens the leave-one-chromosome-out polygenic prediction and so increases association power. The sampled objective is noisy; the local reparameterization trick and antithetic variates reduce its variance.

## Sources

- H. Loya, G. Kalantzis, F. Cooper and P. F. Palamara, "A scalable variational inference approach for increased mixed-model association power", Nature Genetics (2025), Methods ("Bayesian regression with spike-and-slab prior", Eqs. (1)–(4); "Test statistics calculation", Eqs. (5)–(8)), <https://doi.org/10.1038/s41588-024-02044-7>, PMCID PMC11821521.
