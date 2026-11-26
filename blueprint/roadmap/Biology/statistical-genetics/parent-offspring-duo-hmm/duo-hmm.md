# Duo hidden Markov model for parent-child haplotype gene flow

Let $p = (p_1, p_2)$ and $c = (c_1, c_2)$ be the estimated haplotypes of a parent and a child at $L$ ordered biallelic sites. The hidden inheritance state at site $l$ is $S_l = (j, k) \in \{1,2\}^2$, meaning parental haplotype $j$ and child haplotype $k$ are IBD; write $A = (1,1)$, $B = (2,1)$, $C = (1,2)$, $D = (2,2)$, with $P(S_1 = s) = 1/4$. Between sites $l$ and $l+1$, three independent events can occur: a parental switch error with probability $\delta_1$ or a recombination in the transmitting meiosis with probability $\rho_l = 1 - e^{-r_l}$ ($r_l$ the genetic distance), each flipping $j$, and a child switch error with probability $\delta_2$, flipping $k$. The sixteen transitions split into

$$T_1 = \{(u,u)\}, \quad T_2 = \{(A,B),(B,A),(C,D),(D,C)\}, \quad T_3 = \{(A,C),(B,D),(C,A),(D,B)\}, \quad T_4 = \{(A,D),(B,C),(C,B),(D,A)\},$$

changing nothing, only $j$, only $k$, or both. Emissions allow genotyping error $\varepsilon$: $P(p_l, c_l \mid S_l = (j, k)) = 1 - \varepsilon$ if $p_{jl} = c_{kl}$ and $\varepsilon$ otherwise.

Under these assumptions, with $q_l = \rho_l(1 - \delta_1) + (1 - \rho_l)\delta_1$ the probability that $j$ flips, the transition probabilities are $(1-q_l)(1-\delta_2)$, $q_l(1-\delta_2)$, $(1-q_l)\delta_2$ and $q_l\delta_2$ on $T_1, \dots, T_4$, and the joint probabilities that include a recombination are

$$P(S_{l+1} = v, R = 1 \mid S_l = u) = \begin{cases} (1-\delta_2)\,\delta_1\,\rho_l & (u,v) \in T_1 \\ (1-\delta_2)(1-\delta_1)\,\rho_l & (u,v) \in T_2 \\ \delta_2\,\delta_1\,\rho_l & (u,v) \in T_3 \\ \delta_2\,(1-\delta_1)\,\rho_l & (u,v) \in T_4. \end{cases}$$

The posterior probability of a recombination between heterozygous parental sites $l$ and $l+m$ is $\sum_{u,v}$ of forward probability $\times$ this term $\times$ backward probability, normalized by the data likelihood.

## Depends on

- [Lander-Green transition between inheritance vectors](../lander-green-multipoint-pedigree-likelihood/transition.md)

## Expansion

A $T_3$ or $T_4$ step in the Viterbi path implies a child switch error, since a child's haplotype index cannot change by recombination; $T_2$ and $T_4$ steps imply a parental switch error or a true crossover, and in sibships a parental flip shared by most siblings is read as a parental switch error. Intermediate homozygous sites have state-independent emissions, which is why only the flanking forward and backward terms enter the recombination posterior. The state space has 4 states per duo, so the cost is $O(NL)$ for $N$ nonfounders, versus exponential in the number of meioses for a direct Lander-Green computation; $\varepsilon, \delta_1, \delta_2$ are estimated with one forward-backward iteration per duo (Methods, "Duo HMM").

## Sources

- J. O'Connell, D. Gurdasani, O. Delaneau et al., A general approach for haplotype phasing across the full spectrum of relatedness, PLoS Genetics 10 (2014), e1004234. <https://doi.org/10.1371/journal.pgen.1004234> (PMCID PMC3990520)
