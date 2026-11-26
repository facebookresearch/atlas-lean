# Signature-kernel scoring-rule posterior for linked selection coefficients

**Model.** In a discrete-time Wright-Fisher model with $\ell$ biallelic loci (up to $2^\ell$ haplotypes), population size $N$, recombination rates $r_I$ between neighboring loci and diploid fitnesses $w_{ij}$ for haplotype pairs (multiplicative viability selection with coefficients $\theta = (s_A, s_B, s_C, \dots)$), haplotype frequencies $h_{t,i}$ evolve by

$$ \rho_{ij}(t) = \sum_I r_I \bigl( h_{t,i} h_{t,j} - h_{t, i_I j_J} h_{t, j_I i_J} \bigr), \qquad \tilde h_{t+1,i} = \frac{\sum_j w_{ij} \bigl( h_{t,i} h_{t,j} - \rho_{ij}(t) \bigr)}{\sum_{i,j} w_{ij} h_{t,i} h_{t,j}}, $$

followed by drift, $(h_{t+1,1}, \dots, h_{t+1,2^\ell}) \sim \frac{1}{2N} \mathrm{Multinomial}(2N, \tilde h_{t+1})$, where $i_I j_J$ denotes the recombinant haplotype. The data $\mathbf{x}$ are the allele-frequency trajectories of the selected loci at $K+1$ sampling times. The likelihood is intractable but the model is easy to simulate.

**Scoring-rule posterior.** For a scoring rule $S(P_\theta, \mathbf{x})$ and learning rate $w > 0$,

$$ \pi_S(\theta \mid \mathbf{x}^{obs}) \propto p(\theta) \exp\bigl\{ -w\, S(P_\theta, \mathbf{x}^{obs}) \bigr\}. $$

With a symmetric positive-definite kernel $k$, the kernel score $S_k(P_\theta, \mathbf{x}^{obs}) = \mathbb{E}[k(\mathbf{x}, \mathbf{x}')] - 2\, \mathbb{E}[k(\mathbf{x}, \mathbf{x}^{obs})]$, $\mathbf{x}, \mathbf{x}' \sim P_\theta$ independent, has the unbiased estimator from $m$ simulations

$$ \widehat S_k(\mathcal{X}^{\theta,m}, \mathbf{x}^{obs}) = \frac{1}{m(m-1)} \sum_{j \neq q} k(\mathbf{x}^{\theta,j}, \mathbf{x}^{\theta,q}) - \frac{2}{m} \sum_{j=1}^{m} k(\mathbf{x}^{\theta,j}, \mathbf{x}^{obs}). $$

For time-series data the method uses the **signature kernel** $k^{\otimes}(x,y) = \langle \mathrm{Sig}(k_x), \mathrm{Sig}(k_y) \rangle$: trajectories are linearly interpolated into paths, lifted pointwise into the RKHS of a radial basis function kernel, and compared through their signatures (the sequences of iterated path integrals), which characterize a path; the kernel is computed by solving a Goursat partial differential equation.

**Theorem 1.** If $\widehat S(\mathcal{X}^{\theta,m}, \mathbf{x}^{obs}) \to S(P_\theta, \mathbf{x}^{obs})$ in probability as $m \to \infty$, then under mild technical conditions the pseudo-marginal target $\pi^{(m)}_{\widehat S}(\theta \mid \mathbf{x}^{obs}) \propto p(\theta)\, \mathbb{E}\bigl[ \exp\{ -w \widehat S(\mathcal{X}^{\theta,m}, \mathbf{x}^{obs}) \} \bigr]$ converges to $\pi_S(\theta \mid \mathbf{x}^{obs})$ for every $\theta$.

Hence Metropolis-Hastings with a fresh unbiased score estimate at each proposal samples, for large $m$, from the scoring-rule posterior of the joint selection coefficients of linked loci; the same scheme applies to negative frequency-dependent selection and to joint inference of selection coefficients and initial haplotype frequencies.

## Expansion

The kernel score is strictly proper when the kernel is characteristic, so its expectation under the data-generating law is uniquely minimized at the true model, which justifies using it in place of the negative log-likelihood. The signature kernel is characteristic on paths (signatures determine paths up to tree-like equivalence, and the RBF lift preserves this), which makes it suitable for allele-frequency trajectories of several loci observed jointly. The estimator $\widehat S_k$ is a U-statistic and therefore unbiased and consistent as $m \to \infty$; dominated convergence of $\exp\{-w \widehat S\}$ then gives the convergence of the pseudo-marginal target. Joint inference across linked loci captures interference between selected sites through shared haplotypes, which single-locus methods ignore.

## Sources

- Ritabrata Dutta, Yuehao Xu, Sherman Khoo, Francesca Basini, "Signature-Informed Selection Detection: A Novel Method for Multi-Locus Temporal Population Genetic Model", arXiv (2025). Section 2 (Wright-Fisher model with recombination and selection), Section 3 (scoring-rule posterior, Theorem 1, signature kernel score). <https://doi.org/10.48550/arXiv.2512.14353>
