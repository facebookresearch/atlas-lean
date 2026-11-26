# Fractional-depth pileup polishing rule

Let short reads be aligned to an assembly with every alignment of each read reported. For an assembly position $x$, the pileup lists the read nucleotide (a base, or a short string in the case of an insertion) of each alignment covering $x$, after trimming each alignment end (the terminal run of identical bases plus one more base). Let $c_x(\nu)$ be the number of alignments contributing nucleotide $\nu$ at $x$. A read with $a \ge 1$ alignments contributes $1/a$ to the depth of each position that each of its alignments covers, giving the fractional depth $d_x$. With parameters $0 < \phi_{\mathrm{inv}} < \phi_{\mathrm{val}}$ and $n_{\min} \ge 1$ (defaults $\phi_{\mathrm{val}} = 0.5$, $\phi_{\mathrm{inv}} = 0.2$, $n_{\min} = 5$):

- $\nu$ is *valid* at $x$ if $c_x(\nu) > \max(\phi_{\mathrm{val}}\, d_x,\ n_{\min})$;
- $\nu$ is *invalid* at $x$ if $c_x(\nu) < \phi_{\mathrm{inv}}\, d_x$.

The base call at $x$ is replaced by $\nu$ if and only if $\nu$ is the only valid nucleotide, $\nu$ differs from the current call, and every other nucleotide in the pileup is invalid; otherwise the call is kept.

Properties:

- if every read covering $x$ aligns uniquely, then $\sum_\nu c_x(\nu) = d_x$, and with $\phi_{\mathrm{val}} \ge 1/2$ at most one nucleotide can be valid;
- a nucleotide whose count lies between $\phi_{\mathrm{inv}} d_x$ and $\max(\phi_{\mathrm{val}} d_x, n_{\min})$ is neither valid nor invalid; its presence blocks any change, so mixed or low-coverage positions are never edited;
- a read with $a$ alignments contributes total depth $1$ across its alignment sites, so in a repeat with $a$ identical copies the fractional depth is about what best-match alignment would give at a unique site, while each copy still sees the full count of supporting nucleotides.

## Expansion

The rule is a two-threshold vote. Requiring one clear majority and the absence of any intermediate-support alternative makes the polisher conservative: it changes a base only where the reads indicate a single unambiguous alternative, so it rarely introduces errors, and it can be run after other polishers. Counting every alignment lets reads from repeat copies vote at each copy, which fixes errors in repeats that best-match alignment leaves unpolished. When the copies differ, the extra counts can exceed half the fractional depth for more than one nucleotide; the rule then makes no change. The end trimming makes homopolymer-length errors show up as distinct pileup strings.

## Sources

- R. R. Wick, K. E. Holt, "Polypolish: short-read polishing of long-read bacterial genome assemblies", PLoS Computational Biology (2022) e1009802, Results, "Implementation", <https://doi.org/10.1371/journal.pcbi.1009802> (PMC8812927).
