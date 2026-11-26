# HAPMIX local-ancestry hidden Markov model

**Setting.** Let $P_1$ and $P_2$ be phased reference haplotype panels of sizes $n_1, n_2$ from two populations, typed at biallelic sites $1,\dots,S$ with genetic distances $r_1,\dots,r_{S-1}$ (in Morgans) between adjacent sites. An offspring haplotype is sampled from a population formed by a single admixture event $T$ generations ago, with ancestry proportions $\mu_1$ and $\mu_2 = 1-\mu_1$.

**Generative model.**
- *Ancestry.* Ancestry switch points form a Poisson process of rate $T$ per Morgan; each segment between switch points independently has ancestry $i \in \{1,2\}$ with probability $\mu_i$ (so not every switch point changes ancestry).
- *Copying.* Within a segment of ancestry $i$, the offspring is a mosaic of reference haplotypes: at each copy-switch point it copies panel $j = i$ with probability $1-p_i$ and the other panel with the miscopying probability $p_i$, then a haplotype $k$ uniformly from the $n_j$ in that panel; copy-switch points form a Poisson process of rate $\rho_i$ per Morgan.
- *Emission.* If the copied haplotype carries allele $t_{jk} \in \{0,1\}$ at a site, the offspring carries the same allele with probability $1-\theta$ and the other allele with probability $\theta$, where $\theta = \theta_i$ if $j = i$ and $\theta = \theta_3$ (shared by both ancestries) if $j \ne i$.

The hidden state at site $s$ is the triple $(i,j,k)$, giving $2(n_1+n_2)$ states; the process along the genome is a reversible hidden Markov chain with $9$ parameters $T, \mu_1, p_1, p_2, \rho_1, \rho_2, \theta_1, \theta_2, \theta_3$. Posterior ancestry probabilities at each site follow from the forward–backward algorithm, and posterior state paths can be sampled jointly.

**Diploid extension.** For unphased genotypes $g \in \{0,1,2\}$ the hidden state is a pair of haploid states $(i_1,j_1,k_1,i_2,j_2,k_2)$ evolving independently, with the genotype emitted as the sum of the two haploid emissions; this yields posterior probabilities of carrying $0$, $1$ or $2$ alleles of each ancestry and phases the data with respect to ancestry.

## Depends on

- [The Li–Stephens copying model](hmm.md)

## Expansion

With $p_1 = p_2 = 0$ and a single panel the model reduces to the Li–Stephens copying model with recombination parameter $\rho_i$ and mutation parameter $\theta_i$. Many transition probabilities coincide: from any state, the probability of moving to $(l,m,n)$ depends on $(l,m)$ and on whether the haplotype is unchanged, so storing one shared sum per pair $(i,j)$ (four in total) reduces a forward–backward pass from order $4S(n_1+n_2)^2$ to order $2S(n_1+n_2)$, and the diploid pass from order $16S(n_1+n_2)^4$ to order $4S(n_1+n_2)^2$. Nonzero miscopying absorbs incomplete lineage sorting and reference-panel mismatch; without it spurious ancestry breaks appear. Comparing likelihoods across $T$ estimates the time since admixture.

## Sources

- A. L. Price, A. Tandon, N. Patterson, K. C. Barnes, N. Rafaels, I. Ruczinski, T. H. Beaty, R. Mathias, D. Reich, S. Myers, "Sensitive detection of chromosomal segments of distinct ancestry in admixed populations", PLoS Genetics 5 (2009) e1000519, Methods (Eqs (0.1)–(0.3) and "Diploid genotype data from the admixed population"), <https://doi.org/10.1371/journal.pgen.1000519>.
