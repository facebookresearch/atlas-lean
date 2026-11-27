# Causal-locus likelihood ratio by posterior reweighting

In the pooled-sequencing model of a two-parent cross (pool of $N$ segregants, latent pool allele frequencies $x_1, \dots, x_L$ forming a reversible Markov chain along a chromosome with stationary law $\pi(x) = \Pr(N x \sim \mathrm{Bin}(N,\tfrac12))$, and read data $y_i$ depending only on $x_i$), suppose a single block $c$ contains the causal locus and that selection on the phenotype shifts its population allele frequency to $p$, so that $N x_c \sim \mathrm{Bin}(N, p)$ while the conditional law of all other blocks given $x_c$ is unchanged. Write $\Pr(\cdot \mid y)$ for posteriors computed in the null model with no causal locus. Then the data likelihood with causal block $c$ is

$$\Pr(y \mid c, p) = \Pr(y) \sum_{j=0}^{N} \frac{\Pr(x_c = j/N \mid y)}{\pi(j/N)}\, \Pr(x_c = j/N \mid p),$$

and the likelihood-ratio statistic for association at $c$ is

$$\mathrm{LR}(c) = \max_{p'} \frac{\Pr(y \mid c, p')}{\Pr(y \mid c, \tfrac12)} = \max_{p'} \sum_{j=0}^{N} \frac{\Pr(x_c = j/N \mid y)}{\pi(j/N)}\, \Pr(x_c = j/N \mid p').$$

One forward–backward pass of the null model therefore yields the statistic for every candidate block $c$; $\log_{10}\mathrm{LR}(c)$ is a LOD score, its maximiser estimates the causal position, and normalising $\Pr(y \mid c)$ over $c$ under a uniform prior gives approximate credible intervals.

## Depends on

- [Autoregressive model of pool allele frequencies along a chromosome](autoregressive-model-of-pool-allele-frequencies.md)
- [Reversible stochastic matrix](../../../../../Probability/markov-chains/kolmogorov-s-criterion-for-reversibility/is-reversible.md)
- [Smoothed state weights](../../../../../ComputerScience/machine-learning/probabilistic-graphical-models/hidden-markov-models/smoothed.md): the null-model posteriors $\Pr(x_c \mid y)$

## Proof depends on

- [Forward-backward smoothing is a joint-to-likelihood ratio](../../../../../ComputerScience/machine-learning/probabilistic-graphical-models/hidden-markov-models/smoothed-eq.md)
- [Bayes' rule for discrete observations](../../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/bayes-rule/posterior-eq-bayes-posterior.md): $\Pr(y \mid x_c) = \Pr(y)\Pr(x_c \mid y)/\pi(x_c)$

## Expansion

Conditioning on $x_c$ splits the chain into a left and a right part; by reversibility the left part can be written with arrows pointing towards $c$ from both sides, so $\Pr(y \mid x_c)$ is the same function in the causal and null models, and $\Pr(y \mid c, p) = \sum_j \Pr(y \mid x_c = j/N)\Pr(x_c = j/N \mid p)$. Bayes' rule in the null model gives $\Pr(y \mid x_c) = \Pr(y)\Pr(x_c \mid y)/\pi(x_c)$, and at $p = \tfrac12$ the causal model coincides with the null, so $\Pr(y)$ cancels from the ratio. The maximisation over $p'$ is one-dimensional and done numerically; with the continuous Kalman model the sum becomes an integral against Gaussian densities. For replicate experiments selected in opposite directions, the same reweighting gives the ratio of separately maximised likelihoods to a jointly maximised one with a shared $p$. Edwards and Gifford report that this multi-locus treatment improves resolution and accuracy over existing pooled-mapping methods on yeast data sets, localising associations to single genes in several cases.

## Sources

- M. D. Edwards, D. K. Gifford, "High-resolution genetic mapping with pooled sequencing", BMC Bioinformatics 13 (Suppl. 6) (2012), S8, <https://doi.org/10.1186/1471-2105-13-s6-s8> (PMC3358661), Methods, "Inference: discrete model" and "Statistical tests".
