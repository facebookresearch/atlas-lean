# Sufficient read length and coverage for noisy-read assembly

**Model.** A genome of length $G$ consists of an i.i.d. uniform random background on $\{A,C,G,T\}$ together with long *flanked* repeats (approximate repeats whose copies are bordered by independent random sequence). Let $\tilde\ell_{max}$ be the length of the longest flanked repeat, $\tilde\ell_{int}$ the length of the longest pair of flanked interleaved repeats, $\tilde\ell_{tri}$ the length of the longest flanked triple repeat, and $\tilde\ell_{crit} = \max(\tilde\ell_{int}, \tilde\ell_{tri})$. The data are $N$ reads of length $L$ starting at uniformly random positions, each base independently substituted with probability $p$. An algorithm is *$\epsilon$-feasible* at $(N, L)$ if, with probability at least $1 - \epsilon$, it outputs a single contig within edit distance of order $pG$ of the genome.

**Random-overlap length.** Let $(\ell_{iid}, \alpha) = (\ell_{iid}(p, \epsilon/3, G), \alpha(p, \epsilon/3, G))$ solve

$$G^2 \exp\!\bigl(-\ell_{iid}\, D(\alpha \,\|\, \tfrac34)\bigr) = \frac{\epsilon}{6}, \qquad G \exp\!\bigl(-\ell_{iid}\, D(\alpha \,\|\, 2p - \tfrac43 p^2)\bigr) = \frac{\epsilon}{6},$$

where $D(a\|b) = a\log\frac ab + (1-a)\log\frac{1-a}{1-b}$. Overlaps of length at least $\ell_{iid}$ declared by the Hamming threshold $\alpha$ then have total false-positive plus false-negative probability at most $\epsilon/3$; $\ell_{iid}$ is of order tens of bases, while repeat lengths are in the thousands.

**Proposition 1 (greedy).** If $L > \tilde\ell_{max} + 2\ell_{iid}$ and

$$N > \max\left(\frac{G \ln(3/\epsilon)}{L - \tilde\ell_{max} - 2\ell_{iid}},\; \frac{G \ln(3N/\epsilon)}{L - \tilde\ell_{max} - 2\ell_{iid}}\right),$$

greedy merging of reads by decreasing overlap under the repeat-aware overlap rule is $\epsilon$-feasible.

**Proposition 2 (multibridging).** If $L > \tilde\ell_{crit} + 2\ell_{iid}$ and

$$N > \max\left(\frac{G \ln(3/\epsilon)}{L - \tilde\ell_{crit} - 2\ell_{iid}},\; \frac{G \ln(3N/\epsilon)}{L - 2\ell_{iid}}\right),$$

the X-phased Multibridging algorithm is $\epsilon$-feasible. Thus noisy reads need only about $2\ell_{iid}$ extra bases of read length beyond the noiseless requirement that every triple repeat and one repeat of each interleaved pair be bridged, while the coverage term matches Lander–Waterman coverage up to the same shift.

## Expansion

The two equations bound, by Chernoff estimates, the probability that two unrelated length-$\ell_{iid}$ segments look alike (about $G^2$ pairs, per-base mismatch probability $3/4$) and that a true overlap looks too noisy (about $G$ pairs, per-base mismatch probability $2p - \frac43 p^2$ between two noisy copies). The repeat-aware rule inspects both ends of a candidate overlap so that one end falls in a random flank, separating repeat copies. Greedy assembly needs each flanked repeat bridged by a read; multibridging builds a de Bruijn graph with large $K$ and resolves repeats that are only partially bridged, lowering the read-length threshold from $\tilde\ell_{max}$ to $\tilde\ell_{crit}$. The $\ln(3N/\epsilon)/L$ terms ensure coverage of every gap of the required overlap length.

## Sources

- K.-K. Lam, A. Khalak and D. Tse, "Near-optimal assembly for shotgun sequencing with noisy reads", *BMC Bioinformatics* 15 (Suppl. 9) (2014) S4, Eqs. (1)–(2), Proposition 1 (Greedy Algorithm) and Proposition 2 (Multibridging Algorithm). <https://doi.org/10.1186/1471-2105-15-s9-s4> (PMC4168708)
