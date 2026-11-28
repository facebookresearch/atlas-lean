# Potential function for two-locus haploid selection with uniform mutation

Consider a haploid population with two loci, locus 1 with alleles $S_1=\{1,\dots,n\}$ and locus 2 with alleles $S_2=\{1,\dots,n\}$, under linkage equilibrium (weak selection), so that the state is a pair of allele-frequency vectors $(\mathbf{x},\mathbf{y})$ in the product of simplices $\Delta$. The fitness of a genotype $(i,j)$ is $W_{ij}>0$, a fixed positive matrix (a *static environment*); the two loci play a common-interest (coordination) game with payoff matrix $W$. One generation of selection followed by uniform mutation, in which each allele mutates to each other allele with probability $\tau$, maps $(\mathbf{x},\mathbf{y})\mapsto(\mathbf{x}',\mathbf{y}')$ with

$$x'_i = (1-n\tau)\, x_i \frac{(W\mathbf{y})_i}{\mathbf{x}^{\top} W \mathbf{y}} + \tau, \qquad y'_j = (1-n\tau)\, y_j \frac{(W^{\top}\mathbf{x})_j}{\mathbf{x}^{\top} W \mathbf{y}} + \tau.$$

Without mutation ($\tau=0$) this is the multiplicative-weights (replicator) update for both loci.

**Theorem.** If $0\le\tau\le 1/n$, then

$$P(\mathbf{x},\mathbf{y}) = \bigl(\mathbf{x}^{\top} W \mathbf{y}\bigr)^{1-n\tau} \prod_{i} x_i^{\tau} \prod_{j} y_j^{\tau}$$

strictly increases along every trajectory unless a fixed point is reached; hence every trajectory converges to the set of equilibria. The equilibria are exactly the points $(\mathbf{p}^*,\mathbf{q}^*)$ with

$$\frac{(W\mathbf{q}^*)_i}{1-\tau/p^*_i} = \frac{\mathbf{p}^{*\top} W \mathbf{q}^*}{1-n\tau} = \frac{(W^{\top}\mathbf{p}^*)_j}{1-\tau/q^*_j} \quad \text{for all } i\in S_1,\ j\in S_2.$$

**Corollary.** Along every nontrivial trajectory, at each step at least one of the mean fitness $\mathbf{x}^{\top}W\mathbf{y}$ or the product of allele frequencies $\prod_i x_i \prod_j y_j$ strictly increases. Mutation therefore trades mean fitness for allelic diversity, which in the source is shown to be what keeps a population alive when the environment $W$ switches at random: without mutation the finite population goes extinct with probability one, while a small positive mutation rate gives survival with high probability.

## Proof depends on

- [Mean fitness never decreases](../../baum-eagon-inequality-for-diploid-selection/diploid-mean-fitness-le-diploid-mean-fit.md)

## Expansion

1. $P$ is (after raising to a rational power and clearing denominators) a polynomial with nonnegative coefficients, homogeneous in each block of variables.
2. Writing $x_i\,\partial_{x_i}\log P = (1-n\tau)\,x_i (W\mathbf{y})_i/(\mathbf{x}^{\top}W\mathbf{y}) + \tau$ shows that the update is exactly the Baum-Eagon growth transform of $P$ applied to each locus.
3. The Baum-Eagon inequality gives $P(\mathbf{x}',\mathbf{y}')>P(\mathbf{x},\mathbf{y})$ unless the point is fixed; fixed points are the stationary points of $P$ on $\Delta$, which yields the displayed equilibrium equations.

## Sources

- Ruta Mehta, Ioannis Panageas, Georgios Piliouras and Prasad Tetali, "Mutation, sexual reproduction and survival in dynamic environments", in *8th Innovations in Theoretical Computer Science Conference (ITCS 2017)*, LIPIcs 67 (2017), 16:1–16:29 (Theorem 20 and Corollary 21, the potential function and its corollary; Theorems 14 and 18, extinction without mutation and survival with mutation). <https://doi.org/10.4230/LIPIcs.ITCS.2017.16>
- Preprint version (the locators in this item follow its numbering): R. Mehta, I. Panageas, G. Piliouras, P. Tetali, *Mutation, sexual reproduction and survival in dynamic environments*, arXiv:1511.01409 (v3: Theorem 7.2 and Corollary 7.3, the potential function and its corollary; Theorems 6.2 and 6.6, extinction without mutation and survival with mutation). <https://doi.org/10.48550/arXiv.1511.01409>
- L. E. Baum, J. A. Eagon, An inequality with applications to statistical estimation for probabilistic functions of Markov processes and to a model for ecology, *Bull. Amer. Math. Soc.* 73 (1967), 360–363. <https://doi.org/10.1090/S0002-9904-1967-11751-8>
