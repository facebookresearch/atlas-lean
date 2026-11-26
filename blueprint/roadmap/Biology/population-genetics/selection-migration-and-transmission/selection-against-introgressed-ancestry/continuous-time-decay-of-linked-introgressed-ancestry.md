# Continuous-time decay of linked introgressed ancestry

A neutral introgressed allele $a$ sits $L$ base pairs from a deleterious allele with selection coefficient $s > 0$; the recombination rate is $r$ per base pair per generation, so linkage breaks at rate $rL$. At admixture the deleterious allele is fixed in the donor and absent from the recipient. While linked, the haplotype's frequency decays at rate $s$; once recombination moves $a$ onto a recipient background its frequency stays constant.

**Formula.** The expected frequency after $T$ generations is

$$f_a(T) = f_a(0)\left(e^{-rLT}e^{-sT} + \int_0^T rL\,e^{-rLt}e^{-st}\,dt\right) = f_a(0)\,\frac{rL + s\,e^{-T(rL+s)}}{rL + s}.$$

As $T\to\infty$, $f_a(T) \to f_a(0)\,\frac{rL}{rL + s}$.

**Segregating deleterious allele.** If the deleterious allele has frequency $f_N$ in the donor and $f_H$ in the recipient before admixture, then

$$f_a(T) = f_a(0)\left(1 - f_N + f_H + (f_N - f_H)\,\frac{rL + s\,e^{-T(rL+s)}}{rL + s}\right).$$

## Proof sketch

The first term is the probability that the two-locus donor haplotype survives intact for $T$ generations times the factor $e^{-sT}$ by which selection has reduced it; the integrand is the probability density that recombination first separates the alleles at time $t$ times the reduction $e^{-st}$ accumulated while linked. The integral equals $\frac{rL}{rL+s}(1 - e^{-(rL+s)T})$, and adding $e^{-(rL+s)T}$ gives the closed form. It is the continuous-time analogue of the discrete-generation recursion, with $(1-s)(1-r)$ replaced by $e^{-(s+rL)}$, and its limit is the gene flow factor to first order in $r$ and $s$. Linked deleterious alleles thus pull a neutral introgressed allele down to a threshold frequency set by its recombination distance, a form of associative overdominance; since the depletion around a weakly deleterious site spans about 1 Mb, weakly deleterious donor alleles deplete introgressed ancestry around conserved regions even without epistatic incompatibilities.

## Sources

- K. Harris and R. Nielsen, "The genetic cost of Neanderthal introgression", Genetics 203 (2016), 881–891, Equations 1–2 and the following paragraph, <https://doi.org/10.1534/genetics.116.186890> (PMC4896200).
