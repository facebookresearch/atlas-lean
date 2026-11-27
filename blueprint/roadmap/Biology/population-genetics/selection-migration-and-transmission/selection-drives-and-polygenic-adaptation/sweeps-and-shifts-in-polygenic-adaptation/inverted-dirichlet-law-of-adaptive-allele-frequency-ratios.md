# Inverted Dirichlet law of adaptive allele-frequency ratios

**Model.** A panmictic haploid population of size $N_e$ carries a binary trait $Z \in \{0, 1\}$ controlled by $L$ biallelic loci: only the genotype carrying the ancestral allele at every locus has $Z = 0$; any derived allele gives $Z = 1$ (complete redundancy). Locus $i$ mutates from ancestral to derived at rate $\mu_i$ per generation, with population-scaled rate $\Theta_i = 2N_e\mu_i$, and there is no back mutation. At $t = 0$ the environment changes and the Malthusian fitness becomes $W(Z) = s_b Z$ with $s_b > 0$.

**Yule approximation of the establishment phase.** Track only derived lineages that leave surviving descendants ("immortal" lineages). New immortal lineages at locus $i$ arise at rate $p_{\mathrm{mut},i} \approx N_e\mu_i \cdot 2s_b = \Theta_i s_b$, and each immortal lineage splits into two at rate $p_{\mathrm{split}} \approx s_b$. With current lineage counts $(k_1, \dots, k_L)$, $k_j \ll N_e$, the next event falls at locus $i$ with probability

$$\frac{k_i\,p_{\mathrm{split}} + p_{\mathrm{mut},i}}{\sum_{j=1}^{L}\big(k_j\,p_{\mathrm{split}} + p_{\mathrm{mut},j}\big)} = \frac{k_i + \Theta_i}{\sum_{j=1}^{L}(k_j + \Theta_j)},$$

independent of $s_b$ and of time.

**Theorem (limit law of frequency ratios).** As $k_1 \to \infty$, the ratios $x_i = k_i/k_1$, $i = 2, \dots, L$, converge in distribution to the inverted Dirichlet law

$$P_{\mathrm{inDir}}[x \mid \Theta] = \frac{1}{B[\Theta]}\prod_{j=2}^{L} x_j^{\Theta_j - 1}\Big(1 + \sum_{i=2}^{L} x_i\Big)^{-\sum_{i=1}^{L}\Theta_i}, \qquad x \in (0,\infty)^{L-1},$$

with $B[\Theta] = \prod_{j=1}^{L}\Gamma(\Theta_j)\big/\Gamma\big(\sum_{j=1}^{L}\Theta_j\big)$. The law depends on the locus mutation rates only, not on the strength of selection.

**Invariance in the deterministic phase.** Once established, allele frequencies at loci in linkage equilibrium follow $\dot p_i = s_b\,p_i(1 - \bar Z)$, so $\frac{d}{dt}(p_i/p_1) = 0$. The frequency ratios fixed during establishment are therefore preserved until the end of the rapid adaptive phase, and the inverted Dirichlet law describes the architecture at the time of observation (the paper shows this also holds under linkage).

## Proof sketch

The transition rule is a multi-colour Pólya urn with immigration: colour $i$ is drawn with probability proportional to its count plus $\Theta_i$, as in [Hoppe's urn](../../../ewens-sampling-formula-and-the-chinese-restauran/hoppe-law.md). By de Finetti, the vector of proportions $k_i/\sum_j k_j$ converges almost surely to a Dirichlet$(\Theta_1, \dots, \Theta_L)$ random vector $(D_1, \dots, D_L)$. The ratios $x_i = D_i/D_1$ are then ratios of independent gamma variables $G_i/G_1$ with $G_i \sim \Gamma(\Theta_i, 1)$; changing variables from $(G_1, \dots, G_L)$ to $(G_1, x_2, \dots, x_L)$ and integrating out $G_1$ gives $\int_0^\infty G_1^{\sum\Theta - 1}e^{-G_1(1 + \sum x_i)}\,dG_1 = \Gamma(\sum\Theta)(1 + \sum x_i)^{-\sum\Theta}$, which yields the density above. The establishment probability $2s_b$ of each new mutant is Haldane's branching-process approximation; it cancels from the urn probabilities.

## Depends on

- [Haldane's approximation $\pi(s) \approx 2s$](../../../haldane-s-survival-probability-of-a-beneficial-m/tendsto-survival-prob-div.md)

## Proof depends on

- [Law of the allelic partition from Hoppe's urn](../../../ewens-sampling-formula-and-the-chinese-restauran/hoppe-law.md)

## Sources

- I. Höllinger, P. S. Pennings and J. Hermisson, "Polygenic adaptation: From sweeps to subtle frequency shifts", *PLoS Genetics* 15 (2019), e1008035, Methods, Equations (1) and (3)–(7), <https://doi.org/10.1371/journal.pgen.1008035> (PMC6443195).
