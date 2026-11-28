# Transmission identities for a drive locus with a resistance modifier

Consider an infinite diploid population with a drive locus (drive allele $A$, wild type $a$) and a resistance locus (resistance allele $R$, sensitive allele $r$), with recombination fraction $c \in [0, \tfrac12]$ between them. Let $Z_{ij}$ ($i, j \in \{0,1,2\}$) be the frequency at meiosis of genotypes carrying $i$ copies of $A$ and $j$ copies of $R$, and split the double heterozygotes into cis ($AR/ar$) and trans ($Ar/aR$) frequencies $Z_{11}^{\mathrm{cis}} + Z_{11}^{\mathrm{tr}} = Z_{11}$. Write $p_a = 1 - p_A$ and $p_R$ for the allele frequencies, $x_{ar}, x_{aR}, x_{Ar}, x_{AR}$ for the haplotype frequencies, and

$$D = x_{ar}\,x_{AR} - x_{aR}\,x_{Ar}$$

for the linkage disequilibrium. Segregation distortion depends on the resistance genotype $G \in \{rr, Rr, RR\}$: an $Aa$ heterozygote with resistance genotype $G$ transmits $A$ with probability $\tfrac12 + \delta_G$, where $0 \le \delta_G \le \tfrac12$ ($\delta_G = \tfrac12$ is complete distortion, $\delta_G = 0$ Mendelian segregation). All other genotypes segregate in Mendelian fashion.

**Proposition.** After transmission (starred quantities),

$$p_a^* = p_a - \bar\delta\, H, \qquad H = Z_{10} + Z_{11} + Z_{12}, \quad \bar\delta = \frac{\delta_{rr} Z_{10} + \delta_{Rr} Z_{11} + \delta_{RR} Z_{12}}{H},$$

$$p_R^* = p_R + 2\,\delta_{Rr}\,\bigl(\tfrac12 - c\bigr)\bigl(Z_{11}^{\mathrm{cis}} - Z_{11}^{\mathrm{tr}}\bigr).$$

If the genotypes were formed by random union of gametes, so that $Z_{11}^{\mathrm{cis}} = 2x_{ar}x_{AR}$ and $Z_{11}^{\mathrm{tr}} = 2x_{aR}x_{Ar}$, then

$$p_R^* = p_R + 4\,\delta_{Rr}\,\bigl(\tfrac12 - c\bigr)\,D .$$

**Corollary.** Transmission changes the frequency of the resistance allele only if all three hold: the loci are linked ($c < \tfrac12$), they are in linkage disequilibrium ($D \ne 0$ under random union), and resistance heterozygotes still allow some distortion ($\delta_{Rr} > 0$). The distortion levels $\delta_{rr}$ and $\delta_{RR}$ of the two resistance homozygotes never enter $p_R^*$. In particular complete dominant resistance ($\delta_{Rr} = \delta_{RR} = 0$) gives $p_R^* = p_R$ whatever the linkage.

## Proof sketch

Write the gamete output of each genotype class. Only drive heterozygotes are distorted; double homozygotes and drive homozygotes contribute their $R$ alleles exactly as under Mendelian segregation. An $Aa\,rr$ or $Aa\,RR$ parent carries the same resistance allele on both haplotypes, so distortion at the drive locus moves no $R$ alleles between gametes; this is why $\delta_{rr}$ and $\delta_{RR}$ drop out. In a double heterozygote the gamete carries $A$ with probability $\tfrac12 + \delta_{Rr}$, and the gamete is non-recombinant with probability $1 - c$, so a cis parent sends $R$ with probability $(1-c)(\tfrac12 + \delta_{Rr}) + c(\tfrac12 - \delta_{Rr}) = \tfrac12 + \delta_{Rr}(1 - 2c)$ and a trans parent with probability $\tfrac12 - \delta_{Rr}(1 - 2c)$. Summing over classes gives the stated $p_R^*$, and summing the $a$-bearing gametes gives $p_a^*$. Under random union $Z_{11}^{\mathrm{cis}} - Z_{11}^{\mathrm{tr}} = 2D$. Intuitively, resistance can gain at transmission only by riding on a drive-bearing haplotype in an incompletely protected heterozygote, which requires the cis/trans imbalance that linkage disequilibrium and tight linkage create.

## Depends on

- [Linkage disequilibrium of a two-locus gamete law](../../../linkage-disequilibrium-and-haldane-s-map-functio/linkage-diseq.md)

## Sources

- R. Gomulkiewicz, M. L. Thies and J. J. Bull, "Evading resistance to gene drives", Genetics (2021), iyaa040, Appendix "Effects of transmission", Equations (10)–(14), and main-text Equations (7)–(8), <https://doi.org/10.1093/genetics/iyaa040> (PMCID: PMC8045728).
