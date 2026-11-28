# Five-state IBD hidden Markov model with phase switching

Let individuals 1 and 2 have phased haplotypes $(1A, 1B)$ and $(2A, 2B)$ along one chromosome with biallelic markers $l = 1, \dots, L$ at genetic positions (in Morgans) with gaps $r_l$ between $l$ and $l+1$. The hidden state at each marker is $s \in \{0, 1, 2, 3, 4\}$: $s = 0$ is **non-IBD**, and $s = 1, 2, 3, 4$ mean that exactly one haplotype pair, $1A/2A$, $1A/2B$, $1B/2A$ or $1B/2B$ respectively, is identical by descent. The transition matrix between consecutive markers is

$$A_{l \to l+1} = \exp(Q\, r_l),$$

where the rate matrix $Q$ has off-diagonal entries

$$Q_{0j} = \mathrm{IBDin}, \quad Q_{j0} = \mathrm{IBDout}, \quad Q_{jj'} = \mathrm{IBDswitch} \qquad (j \ne j' \in \{1,2,3,4\}),$$

and diagonal $Q_{ii} = -\sum_{j \ne i} Q_{ij}$, so rows sum to zero. Thus IBD segments start at rate $\mathrm{IBDin}$ per Morgan into each pair, end at rate $\mathrm{IBDout}$, and $\mathrm{IBDswitch}$ moves between IBD pairs to model phase switch errors. Given [emission likelihoods](haploid-dosage-emission-likelihoods.md) $P(D_l \mid s)$, the forward–backward algorithm gives posterior probabilities $P(s_l = 0 \mid D)$; an IBD segment is called on each maximal run of markers where $P(s_l = 0 \mid D)$ stays below a threshold and whose genetic length exceeds a minimum cutoff, followed by merging of long segments separated by short gaps and filtering of segments with low marker density.

## Depends on

- [Haploid-dosage emission likelihoods for IBD states](haploid-dosage-emission-likelihoods.md)

## Expansion

Expressing transitions through a rate matrix makes them consistent across uneven marker spacing: $\exp(Q(r + r')) = \exp(Qr)\exp(Qr')$, so the model is a continuous-time Markov chain along the genetic map observed at the markers, and the expected IBD segment length is $1/\mathrm{IBDout}$ Morgans in the absence of switches. Only one shared haplotype pair is modelled because sharing of both pairs or among three or more haplotypes is rare for distant relatives, and the goal is long tracts. A jump from $1A/2A$ to $1B/2B$ would need simultaneous phase errors in both individuals and is unlikely, but using a common symmetric switch rate among all four IBD states allows a large computational speed-up.

## Sources

- H. Ringbauer, Y. Huang, A. Akbari, S. Mallick, I. Olalde, N. Patterson and D. Reich, "Accurate detection of identity-by-descent segments in human ancient DNA", Nature Genetics 56 (2024), Methods ("The HMM", "Transition probabilities", Equation 1; "Postprocessing: calling IBD segments"), <https://doi.org/10.1038/s41588-023-01582-w>, PMCID: PMC10786714.
