# Genealogical solution of the migration–recombination equation

**Model.** Individuals carry types at sites $[n]=\{1,\dots,n\}$ and live in demes $\alpha\in L$ (a finite set). Let $\mu_t(\alpha)$ be the type distribution in deme $\alpha$ and $M(\alpha,\beta)$ the backward migration matrix (the probability that an individual in $\alpha$ had its parent in $\beta$). Recombination according to a partition $\delta$ of $[n]$ occurs with probability $r_\delta$ ($\sum_\delta r_\delta=1$) and assembles the offspring from independent parents, one per block. The discrete-time *migration–recombination equation* (MRE) is

$$\mu_{t+1}(\alpha)=\sum_{\delta}r_\delta\bigotimes_{d\in\delta}\sum_{\beta\in L}M(\alpha,\beta)\,\mu^d_t(\beta),$$

where $\mu^d$ is the marginal on the sites in block $d$.

**Theorem (duality and explicit solution).** Let $(\Sigma_t)$ be the *labelled partitioning process*: a Markov chain on partitions of $[n]$ whose blocks carry deme labels, run backward in time; in each step every block is split according to the recombination distribution marginalised to that block, and each resulting piece independently picks a parent deme by $M$ from its current label. With $\mathcal R_{\boldsymbol\delta}(\mu)=\bigotimes_{(d,\lambda)\in\boldsymbol\delta}\mu^d(\lambda)$,

$$\mathbb E\bigl[\mathcal R_{\Sigma_t}(\mu_0)\,\big|\,\Sigma_0=\boldsymbol\delta\bigr]=\mathcal R_{\boldsymbol\delta}(\mu_t),\qquad\text{so}\qquad \mu_t(\alpha)=\mathbb E\bigl[\mathcal R_{\Sigma_t}(\mu_0)\,\big|\,\Sigma_0=\{([n],\alpha)\}\bigr].$$

Equivalently, the vector $(\mathcal R_{\boldsymbol\delta}(\mu_t))_{\boldsymbol\delta}$ evolves linearly by the stochastic transition matrix $T$ of this chain, so the nonlinear MRE is solved by powers $T^t$.

**Theorem (asymptotics).** If $M$ is primitive with stationary distribution $q$ ($q^\top=q^\top M$) and the recombination distribution can eventually separate all sites, then

$$\mu_t(\alpha)\to\mu_\infty(\alpha)=\bigotimes_{i=1}^n\ \sum_{\beta\in L}q(\beta)\,\mu^{\{i\}}_0(\beta)\qquad\text{for every deme }\alpha,$$

geometrically fast and uniformly in $\mu_0$: all demes approach the same linkage-equilibrium state built from the $q$-weighted initial single-site marginals.

## Depends on

- [Haldane linearisation and diagonalisation of discrete-time single-crossover recombination](haldane-linearisation-and-diagonalisation-of-discrete-time-single-crossover-recombination.md)

## Proof depends on

## Expansion

Reading the MRE backward, each site's ancestral line migrates as an independent copy of the chain $M$ once it has been separated from the others by recombination, and lines that are still together move together. Marginalisation consistency (the marginal on any subset of sites obeys its own MRE) makes the process well defined. In the long run the partition becomes the singletons, which is absorbing, and each singleton's label equilibrates to $q$, giving the limit.

## Sources

- Frederic Alberti, Ellen Baake, Ian Letter and Servet Martinez, "Solving the migration-recombination equation from a genealogical point of view", arXiv:2004.08958 (2020), Section 2 (the MRE), Theorems 4.3, 5.1, 6.2 and 7.1, <https://doi.org/10.48550/arXiv.2004.08958>; published in *Journal of Mathematical Biology* 82(5) (2021), article 41, <https://doi.org/10.1007/s00285-021-01584-4>. Locators follow arXiv v2.
