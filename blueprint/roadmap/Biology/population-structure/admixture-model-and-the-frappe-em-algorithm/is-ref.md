# Reference-allele indicator for a genotype copy

For a genotype matrix $g$ with entries $g_{ij} \in \{0, 1, 2\}$ (the number of reference alleles of individual $i$ at SNP $j$) and a copy index $c \in \{0, 1\}$, copy $c$ of $(i, j)$ carries the reference allele if and only if $c < g_{ij}$.
