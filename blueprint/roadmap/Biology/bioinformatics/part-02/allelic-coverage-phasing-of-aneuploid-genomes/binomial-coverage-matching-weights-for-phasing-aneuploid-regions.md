# Binomial coverage-matching weights for phasing aneuploid regions

**Setting.** In an aneuploid region the two homologs have different copy numbers, so reads covering a heterozygous SNP split unevenly between its alleles, and alleles on the same homolog show similar coverage proportions. For SNPs $s_i$ and $s_j$ in different haplotype fragments, with allele coverages $c(s_i^a),c(s_i^b)$ and $c(s_j^a),c(s_j^b)$, set $p_i^a=c(s_i^a)/(c(s_i^a)+c(s_i^b))$, $p_i^b=1-p_i^a$, and $p(s_j^x)=c(s_j^x)/c(s_j)$ with $c(s_j)=c(s_j^a)+c(s_j^b)$.

**Model.** Under the relative phase "$aa|bb$" (allele $a$ of $s_i$ on the same homolog as allele $a$ of $s_j$), $c(s_j^a)$ is binomial with $N=c(s_j)$ trials and success probability $p_i^a$, giving log-likelihood

$$
\ell(aa|bb)=c(s_j^a)\log p_i^a+c(s_j^b)\log p_i^b .
$$

After normalizing by $c(s_j)$, the edge components are

$$
w_i(s_i^a,s_j^a)=\frac{-1}{p(s_j^a)\log p_i^a},\qquad w_i(s_i^b,s_j^b)=\frac{-1}{p(s_j^b)\log p_i^b},
$$

and symmetric components $w_j$ are computed with the roles of $s_i$ and $s_j$ exchanged; the edge weight is $w=w_i+w_j$. The cross edges for "$ab|ba$" are built the same way, and the four weights are normalized to sum to $1$.

**Decision rule.** Let $W_{\rm cis}=w(s_i^a,s_j^a)+w(s_i^b,s_j^b)$ and $W_{\rm trans}=w(s_i^a,s_j^b)+w(s_i^b,s_j^a)$. The edges between $s_i$ and $s_j$ are retained only if $\min(W_{\rm cis},W_{\rm trans})/\max(W_{\rm cis},W_{\rm trans})$ is below a threshold (0.4 in the original pipeline). Phasing the resulting coverage matching graph is a minimum multiple s-t cut.

## Expansion

Each normalized term is negative, so its negated reciprocal is a positive weight that grows as the observed proportion at $s_j$ better matches the proportion predicted from $s_i$. Normalizing by total coverage removes locus-level biases of Hi-C coverage (GC content, mappability, restriction-site density), leaving only the allelic ratio. In balanced regions ($p\approx 1/2$) both phases receive similar weight and the ambiguity filter drops the edges, which is why such regions need linkage-disequilibrium information instead. A related coverage-ratio scan corrects switch errors inside fragments, using prefix and suffix counts of SNPs whose coverage favors each haplotype.

## Depends on

- [NP-hardness of the minimum multiple s-t cut problem](np-hardness-of-the-minimum-multiple-s-t-cut-problem.md)

## Sources

- Pan W, Gong D, Sun D, Luo H. HICANCER: accurate and complete cancer genome phasing with Hi-C reads. *Scientific Reports* 11 (2021) 6609. <https://doi.org/10.1038/s41598-021-86104-6>. PMCID: PMC7987978. Methods, Step 3 (switching error correction; assembly of haplotype fragments and gap filling).
