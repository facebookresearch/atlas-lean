# Number of reads needed to cover every haplotype above a frequency

Under the Lander–Waterman model with $N$ reads of length $L$ placed uniformly and independently on a genome of length $n$, a haplotype present at frequency $\rho$ receives coverage $c\rho$ with $c = NL/n$, and the probability that all of its $n$ positions are covered is approximately $(1 - e^{-c\rho})^{n}$. Requiring this probability to be at least $p \in (0, 1)$ for every haplotype of frequency at least $\rho$ gives the read-count condition

$$N \ge -\frac{n \ln\bigl(1 - p^{1/n}\bigr)}{\rho L}.$$

For $n = 1000$, $L = 100$ and $p = 0.99$ this requires $N \ge 2302$ reads for $\rho = 0.05$ and $N \ge 11{,}508$ for $\rho = 0.01$; the bound scales linearly in $1/\rho$.

## Depends on

- [Lander–Waterman limit for the uncovered fraction](../../lander-waterman-coverage-model/tendsto-normalized-count-uncovered.md)
- [Read graph and minimal path cover of explaining haplotypes](read-graph-and-minimal-path-cover-of-haplotypes.md)

## Expansion

In the Lander–Waterman limit a position of a haplotype at coverage $c\rho$ is missed with probability $e^{-c\rho}$; treating positions as independent gives the product form, and solving $(1 - e^{-NL\rho/n})^n \ge p$ for $N$ gives the bound. Full coverage of a haplotype by its own reads is what makes it appear as an $s$–$t$ path in the read graph, so the condition guarantees that the completely consistent haplotypes form an explaining set; if it fails, reads from rare haplotypes or residual errors break the path condition and are discarded, which is why the attainable resolution is a function of the number of reads. In low-diversity regions far fewer reads suffice, because reads shared by several haplotypes cover all of them at once.

## Sources

- Eriksson N, Pachter L, Mitsuya Y, Rhee SY, Wang C, Gharizadeh B, Ronaghi M, Shafer RW, Beerenwinkel N. Viral population estimation using pyrosequencing. *PLoS Computational Biology* 4:e1000074 (2008), Results, "Error correction", "Haplotype reconstruction" and "Haplotype frequency estimation", and Methods, "Statistical tests for error correction", equation (1). DOI <https://doi.org/10.1371/journal.pcbi.1000074>. PMCID PMC2323617.
