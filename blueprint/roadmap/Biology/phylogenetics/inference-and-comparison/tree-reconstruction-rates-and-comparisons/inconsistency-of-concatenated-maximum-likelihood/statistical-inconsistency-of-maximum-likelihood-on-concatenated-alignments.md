# Statistical inconsistency of maximum likelihood on concatenated alignments

**Setting.** A species tree with unrooted topology $T$ and branch lengths $L$ (combining time and effective population size on each branch) generates gene trees by the multispecies coalescent. For each of $g$ loci, an alignment of length $\ell = \ell(g)$ evolves i.i.d. along that locus's gene tree under the symmetric $r$-state substitution model with rate $\theta$. Concatenation analysis takes the maximum-likelihood tree $T_{ML}$ of the concatenated alignment $A_1A_2\cdots A_g$, assuming all sites evolve i.i.d. on a single tree under the same model with optimized branch lengths. Let $P(T, L, r, g, \ell, \theta)$ be the probability that $T$ is (one of) the ML topologies.

**Theorem (positive misleadingness).** There exist species trees $(T, L)$ and a sufficiently small substitution rate $\theta$ such that for every $\delta > 0$ there is $g_0$ with

$$P(T, L, r, g, \ell, \theta) \le \delta \qquad \text{for all } g \ge g_0 \text{ and all sequence-length functions } \ell = \ell(g).$$

So adding loci makes concatenated maximum likelihood converge to a wrong topology. Unlimited data, in loci and in sites per locus, cannot rescue it.

**Key lemma.** For the two unrooted binary shapes on six leaves, the caterpillar $Z$ (two cherries) and the symmetric tree $Y$ (three cherries), consider a site pattern $\chi$ generated on a Kingman coalescent tree on the six leaves under the infinite-alleles model with small scaled mutation rate $\theta = \epsilon$. Then

$$\mathbb E\bigl[\mathrm{pars}_Z(\chi) - \mathrm{pars}_Y(\chi)\bigr] = \frac{1}{60}\,\epsilon + O(\epsilon^2),$$

where $\mathrm{pars}_W(\chi)$ is the parsimony score of $\chi$ on $W$. By Ewens' sampling formula, the allele configurations with one allele of size $2$ and one of size $4$, and with two alleles of size $3$, have probabilities $\frac34\epsilon + O(\epsilon^2)$ and $\frac13\epsilon + O(\epsilon^2)$.

## Expansion

In the anomaly zone of the multispecies coalescent, the most frequent gene tree differs from the species tree. That alone does not make concatenation fail, so the proof compares expected likelihood scores. At low substitution rates, the per-site log-likelihood of a tree is, up to a common factor, $-\log(1/\theta)$ times the parsimony score plus lower-order terms. The tree with the smaller expected parsimony score therefore wins once there are many sites. Choosing a six-taxon species tree in which coalescence is fast enough that the data behave nearly like a single coalescent sample, the lemma shows that the wrong shape scores better by an amount of order $\epsilon$. Concentration over $g$ independent loci turns this expectation gap into a wrong ML tree with probability tending to $1$, whatever $\ell(g)$ is.

## Sources

- Sebastien Roch, Mike Steel, "Likelihood-based tree reconstruction on a concatenation of alignments can be positively misleading", arXiv (2014). Section 2 (model, Theorem 1), Section 3 (Ewens sampling computations, Proposition 1), Section 4 (proof of Theorem 1). <https://doi.org/10.48550/arXiv.1409.2051>. Published version: "Likelihood-based tree reconstruction on a concatenation of aligned sequence data sets can be statistically inconsistent", Theoretical Population Biology 100 (2015), 56–62, <https://doi.org/10.1016/j.tpb.2014.12.005>; locators above refer to the arXiv version.
