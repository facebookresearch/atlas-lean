# Haplotype-based population coverage of a peptide vaccine

Consider three linked loci with $M_A$, $M_B$ and $M_C$ alleles, and a population in which the
haplotype $A_i B_j C_k$ has frequency $G(i,j,k) \ge 0$ with
$\sum_{i=1}^{M_A} \sum_{j=1}^{M_B} \sum_{k=1}^{M_C} G(i,j,k) = 1$. Assuming the two inherited
haplotypes are independent, the frequency of the genotype formed by haplotypes
$A_{i_1} B_{j_1} C_{k_1}$ and $A_{i_2} B_{j_2} C_{k_2}$ is

$$F_{i_1 j_1 k_1 i_2 j_2 k_2} = G(i_1, j_1, k_1)\, G(i_2, j_2, k_2).$$

Let $e(a)$ be the number of vaccine peptides predicted to bind allele $a$, and let the genotype's
hit count be the sum over its distinct alleles, of which there are between three and six depending
on zygosity at each locus,

$$C_{i_1 j_1 k_1 i_2 j_2 k_2} = \sum_{a \in \{A_{i_1}, B_{j_1}, C_{k_1}\} \cup \{A_{i_2}, B_{j_2}, C_{k_2}\}} e(a).$$

Then the distribution of the per-individual hit count $n$ in the population is

$$P(n = k) = \sum_{i_1, j_1, k_1} \sum_{i_2, j_2, k_2} F_{i_1 j_1 k_1 i_2 j_2 k_2}\; \mathbf{1}\{C_{i_1 j_1 k_1 i_2 j_2 k_2} = k\},$$

and the coverage of the peptide set at a required display level $N$ is
$P(n \ge N) = \sum_{k \ge N} P(n = k)$.

## Depends on

- [Offspring genotype law under random union of gametes](../offspring.md)
- [Hardy–Weinberg proportions](../offspring-apply.md)

## Expansion

Computing coverage from allele frequencies locus by locus assumes independence between the loci and
therefore misstates the frequency of the allele combinations that actually occur, because the
classical HLA loci are in strong linkage disequilibrium; using measured haplotype frequencies with
random union of haplotypes keeps that structure while making only the Hardy-Weinberg assumption
about pairing. Taking $P(n \ge N)$ as an objective function, rather than the probability of at
least one displayed peptide, selects peptide sets whose coverage is robust: each recipient is
expected to display several of them, so the design does not fail for an individual whose single
covering allele turns out not to be immunogenic.

## Sources

- G. Liu, B. Carter, T. Bricken, S. Jain, M. Viard, M. Carrington, D. K. Gifford, "Computationally
  optimized SARS-CoV-2 MHC class I and II vaccine formulations predicted to target human
  haplotype distributions", Cell Systems 11 (2020) 131-144, Eqs. (1)-(3),
  <https://doi.org/10.1016/j.cels.2020.06.009> (PMC7384425).
