# Hierarchical Bayesian posterior for species trees from multilocus data

Let $D = (d_1, \dots, d_n)$ be sequence alignments at $n$ loci sampled from individuals of several
species, assume no recombination within a locus and free recombination between loci, and let
$g_i$ be the gene tree (with branch lengths) of locus $i$. Let $S$ be the complete species tree:
topology, divergence times and branch population sizes, together with the hyperparameters of its
prior. The hierarchical model draws $S$ from a prior density $P(S)$, then the gene trees independently
given $S$ with the
[multispecies coalescent density](gene-tree-density-under-the-multispecies-coalescent-with-branch-population-functions.md)
$P(g_i \mid S)$, then the alignments independently given the gene trees with the
[Felsenstein likelihood](../../phylogenetics/felsenstein-s-pruning-algorithm/likelihood.md)
$P(d_i \mid g_i)$ of alignment $i$ under a substitution model (the product of its site likelihoods).
The joint posterior then has the unnormalized kernel

$$K_D(S, g_1, \dots, g_n) = P(S)\prod_{i=1}^{n} P(d_i \mid g_i)\, P(g_i \mid S),$$

with normalizing integral $Z(D) = \int K_D(S, g_1, \dots, g_n)\, dS\, dg_1 \cdots dg_n$. If
$0 < Z(D) < \infty$, the joint posterior is the probability density $K_D / Z(D)$, and integrating out
the gene trees, which are nuisance parameters, gives the posterior density of the species tree,

$$P(S \mid D) = \frac{1}{Z(D)}\, P(S)\prod_{i=1}^{n} \int P(d_i \mid g_i)\, P(g_i \mid S)\, dg_i .$$

If $Z(D) = \infty$, $K_D$ is still a kernel but defines no posterior probability law. A proper prior
gives $Z(D) \le 1$, since each $P(d_i \mid g_i) \le 1$ and each $P(\,\cdot \mid S)$ integrates to $1$.

The prior factorizes as $P(S) = f_{BD}(S)\, P_N(S)$: a uniform prior on ranked labelled topologies
together with the reconstructed birth-death density $f_{BD}$ of the divergence times (birth rate
$\lambda$, death rate $\mu$, themselves given hyperpriors), and a prior $P_N$ on population sizes.
With constant size per branch, the sizes are independent draws from a gamma distribution of shape $2$
and scale $\psi$,

$$p(N_b \mid \psi) = \frac{N_b}{\psi^2}\, e^{-N_b/\psi}, \qquad N_b > 0,$$

with mean $2\psi$ and the scale-invariant hyperprior $p(\psi) \propto 1/\psi$. This hyperprior is
improper, so propriety of the posterior depends on the data: with wholly uninformative alignments,
$P(d_i \mid g_i)$ constant in $g_i$, the gene trees integrate out to a constant and
$Z(D) \propto \int_0^\infty d\psi / \psi = \infty$. In the linear-size model the tip sizes get a gamma
prior of shape $4$, the law of the sum of two independent shape-$2$ gammas, so that every most recent
population size, extant or ancestral, has the same prior.

## Depends on

- [Gene tree density under the multispecies coalescent with branch population functions](gene-tree-density-under-the-multispecies-coalescent-with-branch-population-functions.md)
- [Site likelihood of a phylogenetic tree](../../phylogenetics/felsenstein-s-pruning-algorithm/likelihood.md)

## Expansion

The kernel is Bayes' formula for the hierarchical model: the prior density times the conditional
densities of the gene trees given $S$ and of the alignments given the gene trees. The integral over
gene trees cannot be evaluated directly, so the joint posterior is sampled by Markov chain Monte Carlo
over $(S, g_1, \dots, g_n)$, and the species tree marginal is read off the chain; a chain targeting a
kernel with $Z(D) = \infty$ has no stationary probability law to converge to. Compared with two-step
methods that first estimate gene trees and then a species tree, joint inference propagates gene tree
uncertainty and lets the coalescent prior pull poorly resolved gene trees toward the species tree.
Information about the size of an extant species comes from coalescences inside its branch, which is
why at least two individuals per species are needed to estimate it.

## Sources

- J. Heled, A. J. Drummond, "Bayesian inference of species trees from multilocus data", Molecular
  Biology and Evolution 27 (2010) 570-580, Methods, Eqs. (1) and (4)-(6),
  <https://doi.org/10.1093/molbev/msp274> (PMC2822290).
