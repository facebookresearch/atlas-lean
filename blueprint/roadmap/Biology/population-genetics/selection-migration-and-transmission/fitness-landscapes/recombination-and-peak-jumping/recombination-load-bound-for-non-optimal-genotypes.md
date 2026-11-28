# Recombination-load bound for the non-optimal genotype class

Let $w : \Sigma^L \to \mathbb{R}$ be a fitness landscape on $L$-locus genotypes over a finite allele alphabet $\Sigma$, and let $g_{\max}$ be the genotype of maximal fitness. Let $r \in [0,1]$ be the recombination rate, read deterministically as in the source: in a recombination step, a proportion $r$ of the individuals of each genotype class recombines (in particular, exactly $rM$ of the $M$ individuals with genotypes in $\Sigma^L \setminus \{g_{\max}\}$), the recombining individuals are paired among themselves, each pair is replaced by its two recombinant offspring, and the other individuals are unchanged. Then, as a result of recombination alone, the number of individuals carrying a genotype in $\Sigma^L \setminus \{g_{\max}\}$ increases by at most a factor $1 + r$ (Crona 2018, Lemma 1).

If instead each individual recombined independently with probability $r$, the number of non-optimal recombiners would be random and the factor $1 + r$ would hold only in expectation, not surely.

## Expansion

Recombining pairs are of three types: $\{g_{\max}, g_{\max}\}$, which produce only $g_{\max}$; $\{g, g'\}$ with $g, g' \neq g_{\max}$, which cannot increase the count of non-optimal genotypes because each pair yields two offspring; and mixed pairs $\{g_{\max}, g\}$, which can yield at most two non-optimal offspring, i.e. one more than before. Each mixed pair contains one of the $rM$ non-optimal recombiners, so there are at most $rM$ mixed pairs and the count rises from $M$ to at most $M + rM = (1 + r)M$; the worst case is that every non-optimal recombiner is paired with $g_{\max}$.

## Sources

- K. Crona, *Recombination and peak jumping*, PLoS ONE 13(3) (2018), e0193123, Lemma 1. <https://doi.org/10.1371/journal.pone.0193123> (PMCID: PMC5832230)
