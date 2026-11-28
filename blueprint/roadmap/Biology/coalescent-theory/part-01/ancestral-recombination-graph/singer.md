# SINGER

SINGER (Deng, Nielsen and Song 2025) samples genome-wide ancestral recombination graphs from an approximate posterior by Markov chain Monte Carlo. Like ARGweaver it adds the $n$th lineage to a partial graph of $n - 1$ genomes by threading, under the sequentially Markov coalescent, but it splits threading into two hidden Markov models: branch sampling, whose hidden states are the joining branches of the marginal trees, and time sampling, whose hidden states are joining times conditional on the sampled branches. The source states that this two-step threading is approximative and that it is much faster than ARGweaver's model, which treats every joining point as a hidden state. Updates are proposed by sub-graph pruning and re-grafting: cuts are introduced in a run of marginal trees and the pruned subtrees are re-grafted by solving the threading problem for the sub-graph above the cuts. After initialization and every thinning step, ARG re-scaling applies a monotone transformation of node times so that the expected numbers of mutations in time intervals match the observed counts.

## Expansion

1. The prior (a sequentially Markov coalescent approximation) and the mutation model.
2. Branch sampling along the genome, and time sampling conditional on the joining branches.
3. Sub-graph pruning and re-grafting as a Metropolis–Hastings proposal, with its acceptance probability.
4. The ARG re-scaling map on node times.
5. Validity of each update (the output is a graph whose marginal trees are trees on the samples) and the distribution each step samples; the gap between the two-step threading and the joint conditional law of branch and time.

## Sources

- Y. Deng, R. Nielsen and Y. S. Song, Robust and accurate Bayesian inference of genome-wide genealogies for hundreds of genomes, Nat. Genet. 57 (2025), 2124–2135, Results (Fig. 1) and Methods (ARG re-scaling, SGPR). <https://doi.org/10.1038/s41588-025-02317-9>
