# Discretized sequentially Markov coalescent and ARG threading

**Discretized sequentially Markov coalescent (DSMC).** Fix a maximum time $s_{\max} > 0$, a number of intervals $K$ and a tuning parameter $\delta > 0$. The DSMC requires every coalescence and recombination event to occur at one of the time points

$$s_i = \frac{1}{\delta}\Bigl(\exp\Bigl(\frac{i}{K}\ln(1 + \delta\, s_{\max})\Bigr) - 1\Bigr), \qquad i = 0, 1, \dots, K,$$

so that $s_0 = 0$, $s_K = s_{\max}$, and the points are uniformly spaced on a logarithmic scale, densest near the leaves; larger $\delta$ clusters them more strongly near $0$. Sequence positions are integers, at most one recombination occurs between adjacent sites, and given the sequence of local trees $T_1, \dots, T_L$ the alignment columns $D_1, \dots, D_L$ are generated independently, each by a substitution model on its local tree. The DSMC is a hidden Markov model whose hidden state at position $i$ is the local tree together with the recombination between $i - 1$ and $i$; it approaches the sequentially Markov coalescent as $K \to \infty$ with every interval length $s_{j+1} - s_j$ shrinking to $0$, provided $s_{\max}$ is large enough that the probability of a coalescence older than $s_{\max}$ is negligible (with $s_{\max}$ held fixed, the limit truncates coalescence at $s_{\max}$ and differs from the SMC). The source states the limit under exactly this condition, "as K → ∞ and each Δs_j → 0, with s_K sufficiently large that the probability of a coalescence event older than s_K is close to zero", and its Results add that "the DSMC approaches the SMC as the number of intervals K and the sequence length L grow large, for fixed N and ρ".

**Threading.** Given an ARG $G_{n-1}$ for $n - 1$ sequences consistent with the DSMC and an $n$-th sequence, the threading problem is to sample an ARG $G_n$ from $\mathbb P(G_n \mid G_{n-1}, D)$ under the DSMC. Every $G_n$ extending $G_{n-1}$ is determined by (i) a coalescence point for the new lineage at each position, namely a branch of the local tree of $G_{n-1}$ together with a time point $s_j$, and (ii) any new recombination points. Conditional on $G_{n-1}$, the sequence of coalescence points is itself a Markov chain along the genome, so threading is an HMM with state space of size $O(nK)$ per position and can be sampled exactly, up to the DSMC assumptions, by stochastic forward–backward traceback. Repeated removal and re-threading of single sequences (or subtrees) gives a Gibbs-type Markov chain Monte Carlo sampler over ARGs.

## Depends on

- [Pairwise sequentially Markov coalescents SMC and SMC′](../../two-locus-coalescent/sequentially-markov-coalescent-smc-smc-pairwise.md)

## Expansion

The time-point formula maps $i/K$ linearly onto $[0, \ln(1 + \delta s_{\max})]$ and inverts $s \mapsto \ln(1 + \delta s)$. The Markov property of the threading chain comes from the DSMC: given the existing local trees, a new recombination on the threaded branch changes only its attachment point, and the transition probabilities depend only on the attachment points at adjacent positions and the given trees there.

## Sources

- M. D. Rasmussen, M. J. Hubisz, I. Gronau and A. Siepel, *Genome-wide inference of ancestral recombination graphs*, PLoS Genet. 10 (2014), e1004342, <https://doi.org/10.1371/journal.pgen.1004342>, PMCID PMC4022496 (sections "The Discretized Sequentially Markov Coalescent" and "The Threading Problem"; time discretization, equation (4) of Methods).
