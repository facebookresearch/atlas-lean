# MSMC2: pairwise composite likelihood under the sequentially Markovian coalescent

Let $h_1,\dots,h_n$ be phased haplotypes sampled from one population (or from two populations), and model the history by piecewise-constant coalescence rates $\lambda_1,\dots,\lambda_K$ on time intervals $[t_{k-1}, t_k)$, i.e. inverse effective population sizes; with two populations there are three rate profiles, for pairs within population 1, within population 2, and across.

**Pairwise model.** For a pair of haplotypes $(a,b)$, the hidden state at each genomic position is the pairwise coalescence time $\tau_{ab}(x)$ of the local genealogy, which under the sequentially Markovian coalescent evolves along the sequence as a Markov chain with transitions caused by recombination, and the observations are the heterozygous and homozygous sites of the pair, emitted with a mutation rate that depends on $\tau_{ab}(x)$. This two-haplotype HMM (as in PSMC) has likelihood $L_{ab}(\lambda)$ computed by the forward algorithm.

**Composite likelihood.** MSMC2 maximizes

$$\mathcal L_{\mathrm{MSMC2}}(\lambda) = \prod_{1 \le a < b \le n} L_{ab}(\lambda)$$

over the rate profiles. Each factor is exact under the sequentially Markovian coalescent for its pair, and the set of pairs describes the whole distribution of pairwise coalescence times rather than only the time to the first coalescence among all $n$ haplotypes. The cross-population and within-population rates combine into the relative cross-coalescence rate, $2\lambda_{12}(t)/(\lambda_{11}(t) + \lambda_{22}(t))$, which lies near one before the populations split and falls to zero after they become isolated.

## Remarks

The original MSMC tracks the first coalescence among all haplotypes; its emission probabilities require the local lengths of leaf branches, estimated by a separate heuristic HMM, which biases rate estimates beyond about four haplotypes and limits the method to about eight. Replacing the joint model by a product over pairs removes that approximation, because a pair's genealogy is fully described by one coalescence time. The product treats pairs as independent although they share genealogy, so it is a composite rather than a full likelihood, and its curvature overstates precision; uncertainty is assessed by resampling, such as bootstrapping genomic blocks. With more haplotypes, more pairs coalesce recently, so resolution improves in the recent past without the loss of ancient signal that MSMC suffers.

## Depends on

- [Pairwise sequentially Markov coalescents SMC and SMC′](../sequentially-markov-coalescent-smc-smc-pairwise.md)
- [Stationary-kernel discretization for pairwise SMC hidden Markov models](../../../../ComputerScience/machine-learning/probabilistic-graphical-models/baum-welch-algorithm/pairwise-smc-hmm-psmc-discretized-tmrca-hidden-s.md)

## Sources

- S. Schiffels and K. Wang, "MSMC and MSMC2: the multiple sequentially Markovian coalescent", in Statistical Population Genomics, Methods in Molecular Biology (2020), Section 1 (subsections on MSMC and MSMC2, Figures 1–4), <https://doi.org/10.1007/978-1-0716-0199-0_7>.
