# Identifiability of fractional copy numbers from read-depth ratios

**Setting.** The genome is partitioned into segments $s = 1,\dots,m$ of lengths $\ell_s$, each with a constant copy-number state $(a_{s,i}, b_{s,i})$ in every clone $i = 1,\dots,n$; clone $1$ is normal with $(a_{s,1},b_{s,1}) = (1,1)$. Total copy number is $c_{s,i} = a_{s,i} + b_{s,i}$. Sample $p$ ($p = 1,\dots,k$) is a mixture with clone proportions $u_{i,p} \ge 0$, $\sum_i u_{i,p} = 1$. The **fractional copy number** of segment $s$ in sample $p$ is

$$f_{s,p} = \sum_{i=1}^n c_{s,i}\,u_{i,p}, \qquad f^A_{s,p} = \sum_i a_{s,i}u_{i,p},\quad f^B_{s,p} = \sum_i b_{s,i}u_{i,p}.$$

The read-depth ratio (RDR) $r_{s,p}$ against a matched normal is proportional to $f_{s,p}$ with an unknown sample-specific factor, and the B-allele frequency $\beta_{s,p}$ splits $f_{s,p}$ into $f^A_{s,p}, f^B_{s,p}$.

**Theorem.** The fractional copy number $f_{s,p}$ of every segment in every sample is uniquely determined by the RDRs $r_{\cdot,p}$ together with either
1. a clonal diploid segment $s'$ with $c_{s',i} = 2$ for every clone $i$; or
2. two clonal segments $s', z'$ with $c_{s',i} = \omega_{s'}$ and $c_{z',i} = \omega_{z'}$ for all tumour clones $i$, such that

    $$r_{s',p}(\omega_{z'} - 2) \ne r_{z',p}(\omega_{s'} - 2) \quad \text{for every sample } p.$$

The scaling does not depend on the remaining entries of the copy-number matrices or on the clone proportions.

## Expansion

Because the RDR is a normalized read count, $f_{s,p} = \lambda_p\,r_{s,p}$ for one unknown $\lambda_p > 0$ per sample. In case 1 every clone, including the normal one, has two copies of $s'$, so $f_{s',p} = 2$ and $\lambda_p = 2/r_{s',p}$. In case 2, with tumour purity $1 - u_{1,p}$, $f_{s',p} = \omega_{s'} - (\omega_{s'}-2)u_{1,p}$ and similarly for $z'$, giving the linear system

$$\lambda_p r_{s',p} + (\omega_{s'}-2)u_{1,p} = \omega_{s'}, \qquad \lambda_p r_{z',p} + (\omega_{z'}-2)u_{1,p} = \omega_{z'},$$

whose determinant $r_{s',p}(\omega_{z'}-2) - r_{z',p}(\omega_{s'}-2)$ is non-zero by hypothesis, so $\lambda_p$ (and the normal proportion) is unique. Case 1 applies without a whole-genome duplication (segments with BAF near $0.5$ in all samples are state $(1,1)$); case 2 applies after a single duplication affecting all clones, where balanced segments are $(2,2)$ and a second group of clonal states such as $(2,0)$ or $(2,1)$ supplies the other equation.

## Sources

- S. Zaccaria, B. J. Raphael, "Accurate quantification of copy-number aberrations and whole-genome duplications in multi-sample tumor sequencing data", Nature Communications 11 (2020) 4301, Methods (HATCHet algorithm; inference of allele-specific fractional copy numbers), Theorem 1 and Supplementary Method 3, <https://doi.org/10.1038/s41467-020-17967-y>, PMCID PMC7468132.
