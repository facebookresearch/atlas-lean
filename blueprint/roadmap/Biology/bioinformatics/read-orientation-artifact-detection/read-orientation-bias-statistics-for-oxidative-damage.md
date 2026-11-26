# Read-orientation bias statistics for oxidative DNA damage (FoxoG and ArtQ)

In paired-end sequencing, oxidation of guanine to 8-oxoguanine during library preparation produces artifactual $G \to T$ changes observed only in the first read of a pair and the complementary $C \to A$ changes observed only in the second read. For a candidate $C \to A$ / $G \to T$ variant supported by $a$ alternate-allele reads, let $a_{\mathrm{ox}}$ be the number of those reads in the artifact orientation ($G \to T$ on read 1 or $C \to A$ on read 2). The **FoxoG** statistic is

$$\mathrm{FoxoG} = \frac{a_{\mathrm{ox}}}{a} \in [0,1].$$

For a true mutation the read in which the change is seen is unrelated to the change, so $a_{\mathrm{ox}} \sim \mathrm{Binomial}(a, \tfrac12)$ and FoxoG concentrates near $\tfrac12$; for an oxidation artifact FoxoG is near $1$. A filter calls a variant artifactual when FoxoG is high relative to the evidence for the variant, measured by the caller's tumour log-odds score, so that low-allelic-fraction calls with extreme orientation bias are removed while real low-fraction mutations are kept.

At the sample level, base calls at reference $C/G$ sites in the damage-prone context are split into alternate calls consistent with the artifact orientation and the mirror-image alternate calls (the same substitution seen in the opposite read). Assuming that errors from all other sources are symmetric between the two orientations, the excess of artifact-consistent over mirror-image calls, divided by the number of base calls, estimates the per-base error rate due to the artifact; **ArtQ** is this rate on the Phred scale, $\mathrm{ArtQ} = -10\log_{10}(\text{rate})$, so that $\mathrm{ArtQ} > 30$ means fewer than one base in a thousand is affected.

## Expansion

Orientation is informative because oxidative damage happens on one physical strand before amplification, and the library structure fixes which sequencing read reports that strand. For real variants both strands carry the change, so either read can report it; under random fragment orientation each alternate read independently lands in the artifact orientation with probability one half. FoxoG is therefore a binomial proportion whose spread shrinks as $a^{-1/2}$, which is why it must be combined with the strength of the variant evidence: at low read support a real variant can show high FoxoG by chance. Costello et al. traced the artifact to acoustic shearing of DNA containing reactive contaminants, confirmed 8-oxoguanine formation, and computed ArtQ for more than 50,000 libraries; filters based on FoxoG and the log-odds score were trained on 31 tumour samples in the $\mathrm{CCG} \to \mathrm{CAG}$ context.

## Sources

- M. Costello, T. J. Pugh, T. J. Fennell, et al., "Discovery and characterization of artifactual mutations in deep coverage targeted capture sequencing data due to oxidative DNA damage during sample preparation", Nucleic Acids Research 41 (2013), e67, <https://doi.org/10.1093/nar/gks1443> (PMC3616734), Results "Discovery and initial characterization of a low allelic fraction artifact" and "Development of a filter-based method for removing oxidation artifacts".
