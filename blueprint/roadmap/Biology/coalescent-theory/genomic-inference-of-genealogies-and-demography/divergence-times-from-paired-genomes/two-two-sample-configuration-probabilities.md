# Sample-configuration probabilities for two gene copies per population

Two populations split from a panmictic ancestral population $t_1$ generations ago along branch 1 and $t_2$ generations ago along branch 2, with no migration afterwards and arbitrary size changes or structure within each daughter branch. Two gene copies are sampled from each population. For branch $k$ let $\alpha_k$ be the probability that its two lineages do not coalesce before reaching the ancestral population, and $\nu_k$ the expected coalescence time given that they do. Assume infinite sites with mutation rate $\mu$ per site per generation, independence of sites, and let $O_{i,j}$ be the event that $i$ of the copies from population 1 and $j$ from population 2 carry the derived allele, with $p_{i,j} = P(O_{i,j})$. Let $T_{4i}$ be the time the ancestral coalescent started from four lineages spends with $i$ lineages and $\tau_i = \mu E[T_{4i}]$.

**Proposition.** To first order in $\mu$,

$$\begin{aligned}
p_{1,0} &= 2(1-\alpha_1)\mu\nu_1 + 2\alpha_1(\mu t_1 + \tau_4) + \tfrac19\alpha_1(4-\alpha_2)(2\tau_2 + 3\tau_3) - \tfrac13\alpha_1\tau_2,\\
p_{2,0} &= (1-\alpha_1)(\mu t_1 + \tau_4 - \mu\nu_1) + \tfrac1{18}(5 - 4\alpha_1 - \alpha_2 + \alpha_1\alpha_2)(2\tau_2 + 3\tau_3) + \tfrac16(\alpha_1 - \alpha_2)\tau_2,\\
p_{1,1} &= \tfrac29\alpha_1\alpha_2(2\tau_2 + 3\tau_3),\\
p_{2,1} &= \tfrac19\alpha_2(1-\alpha_1)(2\tau_2 + 3\tau_3) + \tfrac13\alpha_2\tau_2,
\end{aligned}$$

and $p_{0,1}, p_{0,2}, p_{1,2}$ follow by exchanging the population labels. Moreover

$$\mu(t_1 - t_2) = \tfrac12(p_{1,0} - p_{0,1}) + (p_{2,0} - p_{0,2}) + \tfrac12(p_{2,1} - p_{1,2}).$$

The seven equations cannot separate $\tau_4$ from $\mu t_1$ and $\mu t_2$, and they have more unknowns than independent equations, so extra assumptions (a constant ancestral size, or an outgroup) are needed for estimation.

## Proof depends on

- [Expected coalescent holding time](../../kingman-s-coalescent-and-watterson-s-estimator/integral-t.md)

## Expansion

Condition on whether each pair coalesces in its daughter branch (probabilities $1-\alpha_1$, $1-\alpha_2$): two, three or four lineages enter the ancestral population. A configuration then arises either from a mutation on a daughter branch (probability $\mu$ times the branch length) or from the derived count $A_k$ in the ancestral sample of $k$ lineages; the probability of both is second order. Subsampling reduces $P(A_2 = \cdot)$ and $P(A_3 = \cdot)$ to $b_i = P(A_4 = i)$, for example $P(A_3 = 1) = \tfrac34 b_1 + \tfrac12 b_2$, and under a panmictic ancestor $b_1 = \tfrac23\mu E[T_{42}] + 2\mu E[T_{43}] + 4\mu E[T_{44}]$, $b_2 = \tfrac23\mu E[T_{42}] + \mu E[T_{43}]$, $b_3 = \tfrac23\mu E[T_{42}]$. Substituting gives the displayed probabilities, and the difference identity follows by direct combination.

## Sources

- P. Sjödin, J. McKenna and M. Jakobsson, "Estimating divergence times from DNA sequences", Genetics 217 (2021), iyab008, <https://doi.org/10.1093/genetics/iyab008> (PMC8049563). Section "Theory", Table 2 and Equations 1–2 (derivations in the Appendix).
