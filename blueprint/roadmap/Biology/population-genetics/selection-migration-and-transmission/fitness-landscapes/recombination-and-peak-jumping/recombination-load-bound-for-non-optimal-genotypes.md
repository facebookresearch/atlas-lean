# Recombination-load bound for the non-optimal genotype class

Let $w : \Sigma^L \to \mathbb{R}$ be a fitness landscape on $L$-locus genotypes over a finite allele alphabet $\Sigma$, and let $g_{\max}$ be the genotype of maximal fitness. Suppose each individual recombines with probability $r \in [0,1]$ per generation with a random partner. Then, as a result of recombination alone, the number of individuals carrying a genotype in $\Sigma^L \setminus \{g_{\max}\}$ increases by at most a factor $1 + r$ (Crona 2018, Lemma 1).

## Expansion

Recombining pairs are of three types: $\{g_{\max}, g_{\max}\}$, which produce only $g_{\max}$; $\{g, g'\}$ with $g, g' \neq g_{\max}$, which cannot increase the count of non-optimal genotypes because each pair yields two offspring; and mixed pairs $\{g_{\max}, g\}$, which can yield at most two non-optimal offspring, i.e. one more than before. The worst case is that every recombining pair is mixed, giving the factor $1 + r$.

## Sources

- K. Crona, *Recombination and peak jumping*, PLoS ONE 13(3) (2018), e0193123, Lemma 1. <https://doi.org/10.1371/journal.pone.0193123> (PMCID: PMC5832230)
