# Diploid Li–Stephens model: collapsed forward step and imputed dosage as a posterior mean

Let $K\ge1$ reference haplotypes $h_1,\ldots,h_K$ over sites $0,\ldots,T$ carry alleles $h_k(t)\in\{0,1\}$, and let $\tau_\rho(k,k')=(1-\rho)[k=k']+\rho/K$, $0\le\rho\le1$, be the haploid [copying transition](trans.md). In the diploid model the hidden state at site $t$ is an ordered pair $(k_1,k_2)\in\{1,\ldots,K\}^2$ of copied haplotypes, the two copying processes are independent Markov chains with uniform initial law, so the transition weight is

$$T\bigl((k_1,k_2),(l_1,l_2)\bigr)=\tau_\rho(k_1,l_1)\,\tau_\rho(k_2,l_2),$$

and the observed genotype $y_t\in\{0,1,2\}$ (or a missing value) is emitted from the unordered pair through a law $e_t(y\mid h_{k_1}(t)+h_{k_2}(t))$ depending only on the dosage $h_{k_1}(t)+h_{k_2}(t)$; a missing observation has emission weight $1$. This is a hidden Markov model with $K^2$ states. Its forward variables $\alpha_{t+1}(l_1,l_2)=e_{t+1}(y_{t+1}\mid h_{l_1}(t+1)+h_{l_2}(t+1))\sum_{k_1,k_2}\alpha_t(k_1,k_2)\,T((k_1,k_2),(l_1,l_2))$ satisfy

$$\sum_{k_1,k_2}\alpha_t(k_1,k_2)\,T\bigl((k_1,k_2),(l_1,l_2)\bigr)=(1-\rho)^2\alpha_t(l_1,l_2)+\frac{\rho(1-\rho)}K\bigl(R_t(l_1)+C_t(l_2)\bigr)+\frac{\rho^2}{K^2}S_t,$$

with $R_t(l_1)=\sum_{k_2}\alpha_t(l_1,k_2)$, $C_t(l_2)=\sum_{k_1}\alpha_t(k_1,l_2)$ and $S_t=\sum_{k_1,k_2}\alpha_t(k_1,k_2)$. Hence one forward step costs $O(K^2)$ operations rather than $O(K^4)$.

At a site $t$ whose genotype is not observed, with the true genotype $G_t=h_{k_1}(t)+h_{k_2}(t)$ of the hidden pair at $t$, the imputed dosage

$$\hat d_t=\mathbb E[G_t\mid y]=\sum_{g=0}^2g\,\mathbb P(G_t=g\mid y)$$

is computed from the posterior state probabilities $\alpha_t\beta_t/\sum\alpha_t\beta_t$, and it minimizes the posterior expected squared error $\mathbb E[(G_t-\delta(y))^2]$ over all measurable functions $\delta$ of the observed data $y$. In particular $0\le\hat d_t\le2$, and for $K=1$ the hidden state is constantly $(1,1)$, so $\hat d_t=2h_1(t)$ is deterministic.

## Depends on

- [Li–Stephens copying transition probability](trans.md)
- [The Li–Stephens copying model](hmm.md)

## Proof depends on

- [Collapse of the sum over predecessor haplotypes](sum-mul-trans.md)
- [The likelihood from the forward and backward variables](../../../ComputerScience/machine-learning/probabilistic-graphical-models/hidden-markov-models/likelihood-eq-sum-forward-mul-backward.md)

## Expansion

A full proof page must establish:

- The diploid transition is a stochastic matrix on $\{1,\ldots,K\}^2$ and the model is a hidden Markov model of the conditional genotype law.
- The collapsed forward step, by applying the [haploid collapse](sum-mul-trans.md) in each coordinate, and its $O(K^2)$ cost.
- The posterior state law from forward and backward variables, and the dosage formula.
- Optimality of the posterior mean under squared loss, the bound $0\le\hat d_t\le2$, and the deterministic case $K=1$.

## Sources

- N. Li and M. Stephens, *Modeling linkage disequilibrium and identifying recombination hotspots using single-nucleotide polymorphism data*, Genetics (2003), <https://pmc.ncbi.nlm.nih.gov/articles/PMC1462870/> (the copying model).
- S. R. Browning and B. L. Browning, *Rapid and accurate haplotype phasing and missing-data inference for whole-genome association studies by use of localized haplotype clustering*, American Journal of Human Genetics (2007), <https://biostat.jhsph.edu/~iruczins/teaching/misc/gwas/papers/browning2007.pdf> (phasing and missing-data inference; background).
