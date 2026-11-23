# One generation of diploid viability selection

For a finite set $\iota$ of alleles, a real vector $p$ on $\iota$ and a real matrix $w$ of genotype fitnesses, let

$$p'_i = \frac{p_i\, m_i}{\bar w(p)},$$

with the [marginal fitness](marginal-fitness.md) $m_i$, the [diploid mean fitness](diploid-mean-fitness.md) $\bar w(p)$ and the convention that division by $0$ gives $0$. When $p$ is a probability vector, the fitnesses are nonnegative and $\bar w(p) > 0$, $p'$ are the allele frequencies after one generation of viability selection under random mating, followed by Mendelian transmission of either allele of each survivor.
