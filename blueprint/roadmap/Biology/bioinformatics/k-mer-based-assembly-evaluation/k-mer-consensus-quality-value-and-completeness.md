# k-mer consensus quality value and completeness

**Setting.** Fix $k$. Let $\mathcal{A}$ be the multiset of $k$-mers of a genome assembly, with $K_{\mathrm{total}} = |\mathcal{A}|$, and let $\mathcal{R}$ be the set of $k$-mers present in high-accuracy reads of the same individual. Let $K_{\mathrm{shared}}$ be the number of assembly $k$-mers that occur in $\mathcal{R}$, and $K_{\mathrm{asm}} = K_{\mathrm{total}} - K_{\mathrm{shared}}$ the number found only in the assembly.

**Consensus quality.** Assume the reads cover the whole genome, so that every correct assembly $k$-mer appears in $\mathcal{R}$, and that consensus errors occur independently at each base with probability $E$. A $k$-mer is error-free with probability $(1-E)^k$, so the per-base accuracy is estimated by

$$P = \left(\frac{K_{\mathrm{shared}}}{K_{\mathrm{total}}}\right)^{1/k}, \qquad E = 1 - P = 1 - \left(1 - \frac{K_{\mathrm{asm}}}{K_{\mathrm{total}}}\right)^{1/k},$$

reported on the phred scale as

$$\mathrm{QV} = -10\log_{10} E .$$

QV $30$ corresponds to accuracy $99.9\%$ and QV $40$ to $99.99\%$.

**Completeness.** Call a read $k$-mer reliable if its multiplicity in the reads is at least a threshold $x^*$, the first multiplicity at which the $k$-mer count histogram has positive slope (separating the error peak from the genomic peak). The $k$-mer completeness is the fraction of reliable read $k$-mers that occur in the assembly.

## Expansion

Under independent per-base errors a $k$-mer survives without error with probability $P^k$, so the observed survival fraction $K_{\mathrm{shared}}/K_{\mathrm{total}}$ (a containment score) estimates $P^k$ and its $k$-th root estimates $P$. For small $E$, $E \approx K_{\mathrm{asm}}/(k K_{\mathrm{total}})$: each base error destroys up to $k$ overlapping $k$-mers. The estimate is biased downward when genuine genome sequence is missing from the reads (low or uneven coverage), because correct assembly $k$-mers are then counted as errors, and upward when an erroneous assembly $k$-mer happens to occur in the reads, for example in high-copy repeats. Because nothing is aligned, the measure also covers repeats and low-coverage regions that mapping-based variant calls exclude. With parental reads, the same set operations on inherited haplotype-specific $k$-mers ("hap-mers") give haplotype completeness and phase-block statistics.

## Sources

- A. Rhie, B. P. Walenz, S. Koren and A. M. Phillippy, "Merqury: reference-free quality, completeness, and phasing assessment for genome assemblies", Genome Biology 21 (2020), 245, Methods ("K-mer completeness" and "Consensus quality (QV) estimation"), <https://doi.org/10.1186/s13059-020-02134-9>, PMCID PMC7488777.
