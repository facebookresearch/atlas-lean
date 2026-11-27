# Hudson's algorithm without recombination samples Kingman's coalescent

Let $n \ge 1$. Work at constant population size, without recombination, in coalescent time units in which each unordered pair of lineages merges at rate $1$. Use exact real arithmetic and ideal independent exponential and uniform variates, not a finite-precision or pseudorandom implementation.

Start with the ordered singleton lineages of $n$ labeled samples. When $k \ge 2$ lineages remain, draw $E_k \sim \mathrm{Exp}(1)$ and an independent uniform unordered pair of their current labels $0,\dots,k-1$, wait $T_k=E_k/\binom{k}{2}$, and merge that pair. Use independent draws at different steps. The merged lineage takes the smaller label and the other lineages keep their relative order, as in a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md). Stop after $n-1$ mergers and retain the final one-block partition; no exponential variable of rate zero is drawn.

The output is the ranked labeled history $H$, together with the durations $(T_k)_{k=2}^n$. This pair encodes the genealogy: sample times are zero, a merger's time is the sum of the preceding durations including its own, and each branch length is its parent's time minus its child's time. Its joint law is

$$\mathcal L\bigl(H,(T_k)_{k=2}^n\bigr)=\rho_n\otimes\bigotimes_{k=2}^n\mathrm{Exp}\!\binom{k}{2},$$

where $\rho_n$ is the [random-joining law](../ranked-labeled-histories-of-coalescent-trees/random-joining.md). This is the joint history-and-duration law of Kingman's $n$-coalescent, started from singleton blocks, and hence the simulator samples its genealogy exactly.

## Proof

With the stated relabeling, the independent pair draws are precisely the coordinates of the canonical ranked-history representation, so their law is $\rho_n$. Each $T_k$ has exponential rate $\binom{k}{2}$, and the entire duration vector is independent of the history. The [holding-time and jump-chain theorem](../partition-valued-kingman-coalescent/holding-times-and-jump-chain-of-kingman-s-n-coal.md) gives the same two independent ingredients for the [path process](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md) with [Kingman's partition rate matrix](../partition-valued-kingman-coalescent/partition-rate.md). Applying the same deterministic genealogy reconstruction gives equality of output laws. Independence here refers to the indexed pair draws; the pairs of sample-subsets that they denote depend on earlier mergers.

For $n=1$ both vectors are empty, the genealogy consists of its single sample and its height is zero. With the empty-sample convention $n=0$, the algorithm returns empty vectors and the absorbing empty partition; no most recent common ancestor is asserted. For $n=2$ the time to the most recent common ancestor is $T_2\sim\mathrm{Exp}(1)$, of mean $1$. Every ranked labeled history has probability $\bigl(\prod_{k=2}^n\binom{k}{2}\bigr)^{-1}$ by [uniformity of random joining](../ranked-labeled-histories-of-coalescent-trees/random-joining-singleton-eq-inv.md); this is not a claim of uniformity over unranked tree shapes.

The clock convention matters when comparing formulations: Kelleher, Etheridge and McVean give total common-ancestor rate $k(k-1)$. Without recombination, multiplying their waiting times by $2$ gives the rate-$\binom{k}{2}$ convention used here. Their deletion of completed ancestral material does not change the recorded genealogy; the retained final partition above is a terminal-state convention.

## Depends on

- [Rate matrix of Kingman's partition-valued coalescent](../partition-valued-kingman-coalescent/partition-rate.md)
- [Path of a continuous-time Markov chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md)
- [Ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md)
- [Random joining](../ranked-labeled-histories-of-coalescent-trees/random-joining.md)

## Proof depends on

- [Holding times and jump chain of Kingman's n-coalescent are independent](../partition-valued-kingman-coalescent/holding-times-and-jump-chain-of-kingman-s-n-coal.md)
- [Every ranked history is equally likely under random joining](../ranked-labeled-histories-of-coalescent-trees/random-joining-singleton-eq-inv.md)

## Sources

- J. Kelleher, A. M. Etheridge and G. McVean, "Efficient coalescent simulation and genealogical analysis for large sample sizes", PLoS Computational Biology 12(5) (2016), e1004842, <https://doi.org/10.1371/journal.pcbi.1004842>, section "Hudson's algorithm with sparse trees" (common-ancestor events and recording the genealogy). The equality of laws follows from the canonical holding-time and jump-chain result as above.
