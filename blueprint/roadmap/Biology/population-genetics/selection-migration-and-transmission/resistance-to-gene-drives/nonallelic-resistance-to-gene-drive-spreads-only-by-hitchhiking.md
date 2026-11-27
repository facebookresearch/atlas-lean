# Nonallelic resistance to a gene drive spreads only by hitchhiking

Take the two-locus drive/resistance model of [the transmission identities](transmission-identities-for-a-drive-locus-with-a-resistance-modifier.md) with unlinked loci ($c = \tfrac12$), complete distortion in resistance-free heterozygotes ($\delta_{rr} = \tfrac12$), and complete dominant resistance ($\delta_{Rr} = \delta_{RR} = 0$). Let $H_{rr} = Z_{10}$ be the frequency of resistance-free drive heterozygotes ($Aa\,rr$), assume random union of gametes, and let selection act on gametes after transmission with multiplicative fitnesses: each $A$ multiplies fitness by $1 - s_A$ and each $R$ by $1 - s_R$ ($0 \le s_A, s_R < 1$). With $D = x_{ar}x_{AR} - x_{aR}x_{Ar}$ (so $D < 0$ means that $a$ and $R$ occur together more often than at random), one generation of transmission gives

$$p_a^* = p_a - \frac{H_{rr}}{2}, \qquad p_R^* = p_R, \qquad D^* = \frac{D}{2} - \frac{p_R H_{rr}}{2},$$

and selection then gives

$$p_R' = \frac{p_R^*(1 - s_R)(1 - p_A^* s_A) - D^* s_A (1 - s_R)}{\bar w}, \qquad \bar w = (1 - p_A^* s_A)(1 - p_R^* s_R) + D^* s_A s_R .$$

For costless resistance ($s_R = 0$) this reduces to

$$p_R' = p_R - \frac{s_A}{\bar w}\, D^*, \qquad \bar w = 1 - p_A^* s_A .$$

**Consequences.** (i) Distortion never changes the frequency of resistance directly; it acts on resistance only by creating negative disequilibrium, through the term $-p_R H_{rr}/2$ in $D^*$, which recombination halves every generation. (ii) For $s_A > 0$, costless resistance increases exactly when $D^* < 0$ (if $s_A = 0$ its frequency does not change), that is, when it is associated with the drive-susceptible allele $a$, which enjoys the fitness advantage $s_A$ over $A$: nonallelic resistance spreads only by genetic hitchhiking with $a$. (iii) The same holds for a recessive lethal drive (zygotes $AA$ die before meiosis, $\bar w = 1 - p_A^2$): the survivors have $p_R^{\#} = p_R - D p_A / \bar w$, and with perfect dominant resistance transmission leaves this unchanged, $p_R^* = p_R^{\#}$.

## Proof sketch

With $\delta_{rr} = \tfrac12$ every $Aa\,rr$ gamete carries $A$, so the $a$ allele loses $H_{rr}/2$, and none of these gametes carry $R$, which is why $p_R$ is untouched while the haplotype $aR$ becomes relatively more common, producing $D^* = D/2 - p_R H_{rr}/2$ (the $D/2$ is free recombination). Under gametic selection the $R$ frequency among survivors is $(x_{aR}^* + (1 - s_A) x_{AR}^*)/\bar w$ when $s_R = 0$; substituting $x_{AR}^* = p_A^* p_R^* + D^*$ gives $p_R^* - s_A D^*/\bar w$. For the lethal drive the dead $AA$ zygotes carry $R$ at frequency $p_A x_{AR}$ of all genes, so $p_R^{\#} = (p_R - p_A x_{AR})/(1 - p_A^2) = p_R - p_A D/(1 - p_A^2)$. Gomulkiewicz, Thies and Bull use this to argue that drives whose resistance is loosely linked can evade resistance evolution, and that dominant resistance is the worst case for the engineer.

## Depends on

- [Transmission identities for a drive locus with a resistance modifier](transmission-identities-for-a-drive-locus-with-a-resistance-modifier.md)

## Sources

- R. Gomulkiewicz, M. L. Thies and J. J. Bull, "Evading resistance to gene drives", Genetics (2021), iyaa040, Equations (1)–(6) and Appendix Equations (18)–(19b), (22)–(24), (27), <https://doi.org/10.1093/genetics/iyaa040> (PMCID: PMC8045728).
