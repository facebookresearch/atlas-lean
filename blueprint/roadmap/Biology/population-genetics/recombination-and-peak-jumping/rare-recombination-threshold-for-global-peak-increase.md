# Rare recombination lets the global-peak genotype increase

Let $w : \Sigma^L \to \mathbb{R}_{>0}$ be a fitness landscape, $g_{\max}$ the genotype of maximal fitness $w_{\max}$, and $w'_{\max}$ the second-highest fitness. Consider a population with discrete generations, selection proportional to $w$, and recombination rate $r$. If $g_{\max}$ is present in the population, its proportion is expected to increase in the next generation provided

$$r < \frac{w_{\max} - w'_{\max}}{w_{\max} + w'_{\max}}$$

(Crona 2018, Theorem 1).

The point of the result is peak jumping: on a rugged landscape the global peak may be inaccessible by single mutations from suboptimal peaks, yet obtainable by shuffling alleles of suboptimal peak genotypes. Once recombination has produced $g_{\max}$, a sufficiently low recombination rate prevents recombination from breaking it up faster than selection amplifies it. There is no analogue of this advantage for two-locus systems or smooth landscapes.

## Depends on

- [Recombination-load bound for the non-optimal genotype class](recombination-load-bound-for-non-optimal-genotypes.md)

## Expansion

Write the new proportions as $p_1 = C_1\tilde p_1 / (C_1 \tilde p_1 + C_2 \tilde p_2)$ and $p_2 = C_2 \tilde p_2 / (C_1 \tilde p_1 + C_2 \tilde p_2)$, where $\tilde p_1, \tilde p_2$ are the previous proportions of $g_{\max}$ and of all other genotypes. Non-recombining $g_{\max}$ individuals give $C_1 \ge w_{\max}(1 - r)$, and the recombination-load bound gives $C_2 \le w'_{\max}(1 + r)$. Hence $p_1 > \tilde p_1$ whenever $w_{\max}(1-r) > w'_{\max}(1+r)$, which rearranges to the stated threshold.

## Sources

- K. Crona, *Recombination and peak jumping*, PLoS ONE 13(3) (2018), e0193123, Theorem 1. <https://doi.org/10.1371/journal.pone.0193123> (PMCID: PMC5832230)
