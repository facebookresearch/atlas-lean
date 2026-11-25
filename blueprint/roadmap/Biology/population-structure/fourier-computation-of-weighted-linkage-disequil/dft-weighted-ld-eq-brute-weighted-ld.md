# ALDER's transform algorithm equals the brute-force weighted LD

Let $S$ be a finite set of SNPs with grid cells $c$, genotypes $g_i(x)$ of $m$ individuals and weights $w$, and let $N \ge 1$ and $K$ be natural numbers with $c(x) < K$ for every SNP $x$ and $2K \le N + 1$. Then for every $j < K$,

$$\mathrm{WLD}^{\mathcal{F}}_j = \mathrm{WLD}_j,$$

where the left side is the [transform computation](dft-weighted-ld.md) and the right side the [brute-force weighted LD sum](brute-weighted-ld.md).
