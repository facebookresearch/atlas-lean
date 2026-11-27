# Constrained allele-specific copy-number factorization

**Setting.** For $m$ segments (clusters of lengths $\ell_s$), $n$ clones (clone $1$ normal diploid) and $k$ samples, let $F^A = [f^A_{s,p}]$ and $F^B = [f^B_{s,p}]$ be the $m\times k$ allele-specific fractional copy-number matrices, $A = [a_{s,i}]$, $B = [b_{s,i}]$ non-negative integer $m\times n$ allele-specific copy-number matrices, and $U = [u_{i,p}]$ an $n\times k$ clone-proportion matrix with columns in the probability simplex. In exact form the **allele-specific copy-number factorization (ACF)** problem asks for $A, B, U$ with

$$F^A = AU, \qquad F^B = BU.$$

**Problem (D-CACF).** Given $F^A, F^B$, $n$, a maximum total copy number $c_{\max}$, a minimum clone proportion $u_{\min}$, and $\theta \in \{1,2\}$ ($\theta = 2$ after a whole-genome duplication), minimize

$$D = \|F^A - AU\| + \|F^B - BU\|, \qquad \|F^A - AU\| = \sum_{s=1}^m\sum_{p=1}^k \ell_s\,\Big|f^A_{s,p} - \sum_{i=1}^n a_{s,i}u_{i,p}\Big|,$$

subject to
- $a_{s,i} + b_{s,i} \le c_{\max}$ for all $s, i$;
- $u_{i,p} \ge u_{\min}$ or $u_{i,p} = 0$ for every tumour clone $i$ and sample $p$;
- for every segment $s$, either $a_{s,i} \ge \theta$ for all clones $i$ or $a_{s,i} \le \theta$ for all clones $i$, and the same for $b_{s,i}$ (no allele is amplified in one clone and deleted in another).

## Depends on

- [Identifiability of fractional copy numbers from read-depth ratios](identifiability-of-fractional-copy-numbers-from-read-depth-ratios.md)

## Expansion

Noise in $F^A, F^B$ can make the exact ACF problem infeasible, hence the length-weighted $\ell_1$ objective; the factorization is otherwise underdetermined, hence the three constraints, which are weaker than earlier assumptions (at most two states per segment, or a single aberrant state). The objective separates over segments for fixed $U$, and over samples for fixed $A, B$; coordinate descent alternates the two subproblems with random restarts; an integer linear program solves small instances exactly. The factorization is run for both the no-duplication and duplication scalings, and a model-selection step chooses the number of clones and the presence of a whole-genome duplication jointly, preferring the simplest solution.

## Sources

- S. Zaccaria, B. J. Raphael, "Accurate quantification of copy-number aberrations and whole-genome duplications in multi-sample tumor sequencing data", Nature Communications 11 (2020) 4301, Methods, Problems 1–2 and Supplementary Methods 4–5, <https://doi.org/10.1038/s41467-020-17967-y>, PMCID PMC7468132.
