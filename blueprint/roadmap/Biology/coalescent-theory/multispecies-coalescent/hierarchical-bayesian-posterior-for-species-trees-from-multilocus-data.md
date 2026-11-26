# Hierarchical Bayesian posterior for species trees from multilocus data

Let $D = (d_1, \dots, d_n)$ be sequence alignments at $n$ loci sampled from individuals of several
species, assume no recombination within a locus and free recombination between loci, and let
$g_i$ be the gene tree (with branch lengths) of locus $i$. Let $S$ be the complete species tree:
topology, divergence times and branch population sizes. The joint posterior is

$$P(S, g_1, \dots, g_n \mid D) \ \propto\ P(S)\prod_{i=1}^{n} P(d_i \mid g_i)\, P(g_i \mid S),$$

where $P(d_i \mid g_i)$ is the Felsenstein likelihood of alignment $i$ under a substitution model,
$P(g_i \mid S)$ is the
[multispecies coalescent density](gene-tree-density-under-the-multispecies-coalescent-with-branch-population-functions.md),
and $P(S)$ is the species tree prior. The posterior of the species tree alone is obtained by
integrating out the gene trees, which are nuisance parameters:

$$P(S \mid D) \ \propto\ P(S)\prod_{i=1}^{n} \int P(d_i \mid g_i)\, P(g_i \mid S)\, dg_i .$$

The prior factorizes as $P(S) = f_{BD}(S)\, P_N(S)$: a uniform prior on ranked labelled topologies
together with the reconstructed birth-death density $f_{BD}$ of the divergence times (birth rate
$\lambda$, death rate $\mu$, themselves given hyperpriors), and a prior $P_N$ on population sizes.
With constant size per branch, the sizes are independent draws from a gamma distribution of shape $2$
and scale $\psi$,

$$p(N_b \mid \psi) = \frac{N_b}{\psi^2}\, e^{-N_b/\psi}, \qquad N_b > 0,$$

with mean $2\psi$ and the scale-invariant hyperprior $p(\psi) \propto 1/\psi$. In the linear-size
model the tip sizes get a gamma prior of shape $4$, the law of the sum of two independent shape-$2$
gammas, so that every most recent population size, extant or ancestral, has the same prior.

## Depends on

- [Gene tree density under the multispecies coalescent with branch population functions](gene-tree-density-under-the-multispecies-coalescent-with-branch-population-functions.md)

## Expansion

The integral over gene trees cannot be evaluated directly, so the joint posterior is sampled by Markov
chain Monte Carlo over $(S, g_1, \dots, g_n)$, and the species tree marginal is read off the chain.
Compared with two-step methods that first estimate gene trees and then a species tree, joint
inference propagates gene tree uncertainty and lets the coalescent prior pull poorly resolved gene
trees toward the species tree. Information about the size of an extant species comes from coalescences
inside its branch, which is why at least two individuals per species are needed to estimate it.

## Sources

- J. Heled, A. J. Drummond, "Bayesian inference of species trees from multilocus data", Molecular
  Biology and Evolution 27 (2010) 570-580, Methods, Eqs. (1) and (4)-(6),
  <https://doi.org/10.1093/molbev/msp274> (PMC2822290).
