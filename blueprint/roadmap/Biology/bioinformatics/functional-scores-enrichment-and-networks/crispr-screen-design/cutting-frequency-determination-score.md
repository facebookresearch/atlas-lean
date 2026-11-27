# Cutting frequency determination score as a product of per-mismatch activities

Fix a guide RNA of length $L = 20$ paired to a candidate genomic site. Let $M \subseteq \{1, \dots, L\}$ be the set of positions at which guide and site mismatch, let $t_p$ denote the mismatch type at position $p$ (one of the twelve RNA:DNA pairings, such as rG:dA), and let $a(p, t) \in [0, 1]$ be the measured relative activity of a guide carrying the single mismatch of type $t$ at position $p$, calibrated against the perfectly matched guide; let $a_{\mathrm{PAM}} \in [0, 1]$ be the corresponding relative activity of the protospacer-adjacent motif of the site.

**Definition.** The cutting frequency determination score of the guide–site pair is

$$\mathrm{CFD} \;=\; a_{\mathrm{PAM}} \prod_{p \in M} a(p, t_p) \;\in\; [0, 1],$$

with the empty product equal to $1$, so a perfectly matched site with a canonical motif scores $1$ and every mismatch can only lower the score.

**Interpretation.** The score is the activity predicted by assuming that mismatches act independently and multiplicatively on cutting frequency, with no interaction between positions and no dependence on the number of mismatches beyond the product. It is monotone: adding a mismatch multiplies the score by a factor in $[0,1]$, so $\mathrm{CFD}$ is nonincreasing under enlarging $M$, and the off-target burden of a guide is summarized by counting sites in score tiers, for instance $\mathrm{CFD} = 1$, $0.2 \le \mathrm{CFD} < 1$, $0.05 \le \mathrm{CFD} < 0.2$ and $\mathrm{CFD} < 0.05$.

## Remarks

The per-position activities are estimated from a saturating panel of singly mismatched guides assayed for loss of protein knockout, and the motif factor from the activity of guides against each two-nucleotide motif variant; the model then extrapolates to multiply mismatched sites by the product rule. For example a single rG:dA mismatch at position 6 with activity $0.67$ gives $\mathrm{CFD} = 0.67$, and an rG:dA mismatch at position 7 with activity $0.57$ together with an rC:dT mismatch at position 10 with activity $0.87$ gives $0.57 \times 0.87 = 0.50$. Multiplicativity is an independence assumption, not a derived fact; its justification is empirical, through the rank correlation of the score with read counts at experimentally recovered off-target sites, where it outperformed earlier position-weighted additive scores. A practical caveat is that scoring presupposes enumeration of candidate sites: an aligner that misses multiply mismatched sites removes them from the sum regardless of the quality of the score.

## Sources

- J. G. Doench, N. Fusi, M. Sullender, M. Hegde, E. W. Vaimberg, K. F. Donovan, I. Smith, Z. Tothova, C. Wilen, R. Orchard, H. W. Virgin, J. Listgarten and D. E. Root, "Optimized sgRNA design to maximize activity and minimize off-target effects of CRISPR-Cas9", Nature Biotechnology 34 (2016), 184–191, Methods section "Cutting Frequency Determination (CFD) score" and Fig. 5, <https://doi.org/10.1038/nbt.3437>, PMCID: PMC4744125.
