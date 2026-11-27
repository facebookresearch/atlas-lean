# Genealogies within a fixed pedigree

Wakeley, King, Low and Ramachandran (2012) treat the population pedigree of a diploid biparental population as fixed and model gene genealogies as the percolation of genetic lineages through it by Mendelian inheritance: a lineage in an individual traces to its mother or its father with probability $1/2$ each, independently; two lineages that trace to the same individual coalesce with probability $1/2$; and two distinct lineages in one individual trace one to each parent. The standard derivation of the coalescent instead averages over random reproduction, through the pair coalescence probability $E[\nu_1(\nu_1 - 1)]/(N - 1)$ of a Cannings model (their equation (1)). Conditional on a fixed pedigree the two laws differ. For a pair of individuals whose family trees first share a single common ancestor in generation $g$, the coalescence probability in that generation is

$$\frac{1}{2^{2g+1}},$$

the product of $2^{-g}$ for each lineage to reach that ancestor and $1/2$ for them to coalesce there (equation (2)); and for samples that contain no sibs, first cousins or second cousins, coalescence is impossible in the first three generations. By analysis and simulations on Wright–Fisher pedigrees and on pedigrees built from family data, the differences from the standard coalescent are confined to roughly the most recent $\log_2 N$ generations, and the standard coalescent is often hard to reject statistically.

## Expansion

1. Pedigrees, Mendelian transmission of one gene copy per parent, and the conditional law of the genealogy of a sample given the pedigree.
2. The averaged law over random Wright–Fisher pedigrees and its Kingman limit.
3. The coalescence probability $2^{-(2g+1)}$ at a single first common pedigree ancestor in generation $g$, and its sum over several common ancestors.
4. Explicit small pedigrees (sibs, cousins, unrelated pairs) where the conditional coalescence-time law differs from the averaged one.
5. Dependence between unlinked loci induced by a shared pedigree.

## Sources

- J. Wakeley, L. King, B. S. Low and S. Ramachandran, Gene genealogies within a fixed pedigree, and the robustness of Kingman's coalescent, Genetics 190 (2012), 1433–1445, abstract, Introduction (equation (1)), the description of the simulation model, and equation (2). <https://doi.org/10.1534/genetics.111.135574>
