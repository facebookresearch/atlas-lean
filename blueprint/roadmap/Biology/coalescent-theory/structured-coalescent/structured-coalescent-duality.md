# Duality between structured diffusions and the structured coalescent

In Etheridge's description of a subdivided population (RIMS lectures II), demes $i \in I$ have effective sizes $N_e(i)$, a proportion $m_{ij}$ of deme $i$ migrates to deme $j$ each generation, and migration is conservative, $\sum_jN_e(i)m_{ij} = \sum_jN_e(j)m_{ji}$. Let the sizes and migration proportions depend on a scaling parameter $N$, with limiting relative sizes and scaled migration rates

$$c_i = \lim_{N \to \infty}\frac{N_e(i)}{N} \in (0, \infty), \qquad M_{ij} = \lim_{N \to \infty} N m_{ij} \in [0, \infty),$$

so that conservative migration becomes $\sum_jc_iM_{ij} = \sum_jc_jM_{ji}$. With time in units of $N$ generations, simultaneous migration and coalescence and multiple mergers have probability of order $1/N^2$, and the frequencies $p_i$ of an allele $a$ converge to Kimura's stepping-stone system of Wright–Fisher diffusions coupled by migration,

$$dp_i = \sum_j\frac{c_j}{c_i}M_{ji}(p_j - p_i)\,dt + \sqrt{\frac{p_i(1 - p_i)}{c_i}}\,dW_i,$$

with independent Brownian motions $W_i$. The ancestral lineages of a sample follow the structured coalescent $n = (n_i)_{i\in I}$: a lineage in deme $i$ moves to deme $j$, $n_i \mapsto n_i - 1$ and $n_j \mapsto n_j + 1$, at rate $n_ic_jM_{ji}/c_i$, and two lineages in deme $i$ coalesce, $n_i \mapsto n_i - 1$, at rate $n_i(n_i - 1)/(2c_i)$. With $p^n = \prod_{i\in I}p_i^{n_i}$, the two processes are dual:

$$E\bigl[p_t^{n_0}\bigr] = E\bigl[p_0^{n_t}\bigr],$$

that is, the probability that a sample of $n_i(0)$ genes from each deme $i$ at time $t$ is all of type $a$ equals the expected product of the initial frequencies over the demes occupied by its ancestral lineages. The generator check is a derivation: the diffusion term $\frac{p_i(1 - p_i)}{2c_i}\partial_i^2$ applied to $p_i^{n_i}$ gives $\frac{n_i(n_i - 1)}{2c_i}(p_i^{n_i - 1} - p_i^{n_i})$, the coalescence term, and the migration drift $\sum_j\frac{c_j}{c_i}M_{ji}(p_j - p_i)\partial_i$ applied to $p^n$ gives $\sum_j n_i\frac{c_j}{c_i}M_{ji}(p^{n - e_i + e_j} - p^n)$, the migration term.

## Depends on

- [Transition rates of the two-lineage structured coalescent](../../../Biology/coalescent-theory/structured-coalescent/rate.md)
- [Closed-form mean coalescence times in the island model](../../../Biology/coalescent-theory/structured-coalescent/mean-coalescence-time.md)
- [Moment duality with Kingman's coalescent](../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion/generator-pow.md)

## Expansion

1. The structured Wright–Fisher model with conservative migration and the scaling under which its frequencies converge to the stepping-stone diffusions.
2. The structured coalescent as the limit of the sample genealogy.
3. The generator identity for $p^n$ and the duality theorem.
4. Identity probabilities within and between demes as moments, and their comparison with the island-model mean coalescence times.

## Sources

- A. Etheridge, Some mathematical models from population genetics II. Adding space, lecture slides, RIMS, Kyoto, September 2023 (University of Oxford), slides on the structured Wright–Fisher model, the structured coalescent, Kimura's stepping stone model and its duality.
