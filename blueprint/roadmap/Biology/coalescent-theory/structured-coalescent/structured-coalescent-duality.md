# Duality between structured diffusions and the structured coalescent

Consider a subdivided population in which demes $i \in I$ have effective sizes $N_e(i)$, a proportion $m_{ij}$ of deme $i$ migrates to deme $j$ each generation, and migration is conservative, $\sum_jN_e(i)m_{ij} = \sum_jN_e(j)m_{ji}$. Let the sizes and migration proportions depend on a scaling parameter $N$, with limiting relative sizes and scaled migration rates

$$c_i = \lim_{N \to \infty}\frac{N_e(i)}{N} \in (0, \infty), \qquad M_{ij} = \lim_{N \to \infty} N m_{ij} \in [0, \infty),$$

so that conservative migration becomes $\sum_jc_iM_{ij} = \sum_jc_jM_{ji}$. With time in units of $N$ generations, simultaneous migration and coalescence and multiple mergers have probability of order $1/N^2$, and the frequencies $p_i$ of an allele $a$ converge to the stepping-stone system of Wright–Fisher diffusions coupled by migration,

$$dp_i = \sum_j\frac{c_j}{c_i}M_{ji}(p_j - p_i)\,dt + \sqrt{\frac{p_i(1 - p_i)}{c_i}}\,dW_i,$$

with independent Brownian motions $W_i$ (the stepping-stone model of Kimura and Weiss 1964). The ancestral lineages of a sample follow the structured coalescent $n = (n_i)_{i\in I}$, the deme counts of the [structured coalescent for $n$ lineages](structured-coalescent-for-n-lineages-with-a-gene.md) with the relative sizes $c_i$, $N$ gene copies in the reference population (so that its time unit is the present one of $N$ generations) and backward migration probabilities $q_{ij} = c_jM_{ji}/(Nc_i)$. With that page's rates, each lineage moves from deme $i$ to deme $j$ at rate $Nq_{ij} = c_jM_{ji}/c_i$ and each pair of lineages in deme $i$ coalesces at rate $1/c_i$, so a lineage in deme $i$ moves to deme $j$, $n_i \mapsto n_i - 1$ and $n_j \mapsto n_j + 1$, at rate $n_ic_jM_{ji}/c_i$, and two lineages in deme $i$ coalesce, $n_i \mapsto n_i - 1$, at rate $n_i(n_i - 1)/(2c_i)$; under conservative migration $c_jM_{ji}/c_i$ is the backward migration rate from deme $i$ to deme $j$, and this is the structured coalescent of Notohara (1990) and Wilkinson-Herbots (1998, Eq. (3)), up to the normalization of the scaled migration rates. With $p^n = \prod_{i\in I}p_i^{n_i}$, the two processes are dual (Notohara 1990):

$$E\bigl[p_t^{n_0}\bigr] = E\bigl[p_0^{n_t}\bigr],$$

that is, the probability that a sample of $n_i(0)$ genes from each deme $i$ at time $t$ is all of type $a$ equals the expected product of the initial frequencies over the demes occupied by its ancestral lineages. The generator check is a derivation: the diffusion term $\frac{p_i(1 - p_i)}{2c_i}\partial_i^2$ applied to $p_i^{n_i}$ gives $\frac{n_i(n_i - 1)}{2c_i}(p_i^{n_i - 1} - p_i^{n_i})$, the coalescence term, and the migration drift $\sum_j\frac{c_j}{c_i}M_{ji}(p_j - p_i)\partial_i$ applied to $p^n$ gives $\sum_j n_i\frac{c_j}{c_i}M_{ji}(p^{n - e_i + e_j} - p^n)$, the migration term.

## Depends on

- [Structured coalescent for n lineages with a general migration matrix](structured-coalescent-for-n-lineages-with-a-gene.md)
- [Transition rates of the two-lineage structured coalescent](../../../Biology/coalescent-theory/structured-coalescent/rate.md)
- [Closed-form mean coalescence times in the island model](../../../Biology/coalescent-theory/structured-coalescent/mean-coalescence-time.md)
- [Moment duality with Kingman's coalescent](../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion/generator-pow.md)

## Expansion

1. The structured Wright–Fisher model with conservative migration and the scaling under which its frequencies converge to the stepping-stone diffusions.
2. The structured coalescent as the limit of the sample genealogy.
3. The generator identity for $p^n$ and the duality theorem.
4. Identity probabilities within and between demes as moments, and their comparison with the island-model mean coalescence times.

## Sources

- Original result: M. Notohara, The coalescent and the genealogical process in geographically structured population, J. Math. Biol. 29 (1990), 59–75. <https://doi.org/10.1007/BF00173909>
- H. M. Wilkinson-Herbots, Genealogy and subpopulation differentiation under various models of population structure, J. Math. Biol. 37 (1998), 535–585, Section 2, Eq. (3).
- M. Kimura and G. H. Weiss, The stepping stone model of population structure and the decrease of genetic correlation with distance, Genetics 49 (1964), 561–576. <https://doi.org/10.1093/genetics/49.4.561>
