# Background mutation rate decides sweeps versus shifts

Work in the redundant binary-trait model of the [inverted Dirichlet law of adaptive allele-frequency ratios](inverted-dirichlet-law-of-adaptive-allele-frequency-ratios.md), with equal locus mutation rates $\Theta_i \equiv \Theta_l = 2N_e\mu$ at all $L$ loci and loci in linkage equilibrium.

**Two loci.** Let $x \in [0,1]$ be the ratio of the derived-allele frequency at the minor locus to that at the major locus, observed after the rapid adaptive phase. Its density is the folded beta-prime law

$$P_{\beta'}[x \mid \Theta_l] = \frac{2\,\Gamma(2\Theta_l)}{\Gamma(\Theta_l)^2}\,x^{\Theta_l - 1}(1 + x)^{-2\Theta_l}, \qquad 0 \le x \le 1,$$

independent of the selection coefficients before and after the environmental change and of linkage. For small $\Theta_l$ the mass concentrates near $x = 0$ (a sweep at one locus, $\mathbb{E}[x] \ll 1$); for large $\Theta_l$ it concentrates near $x = 1$ (similar shifts at both loci).

**Many loci.** For $L$ loci define the **background mutation rate**

$$\Theta_{\mathrm{bg}} = (L - 1)\,\Theta_l,$$

the total population-scaled mutation rate at all loci other than the major one. The ratio of the first minor locus to the major locus is approximately distributed as in the two-locus formula with $\Theta_l$ replaced by $\Theta_{\mathrm{bg}}$: adaptation is sweep-like when $\Theta_{\mathrm{bg}} \lesssim 1$ and shift-like when $\Theta_{\mathrm{bg}} \gg 1$, largely irrespective of the strength of selection.

**Joint frequencies at a given adaptive progress.** If the phenotypic progress is measured by the remaining frequency $f_w = \prod_{j=1}^{L}(1 - p_j)$ of the ancestral genotype, the joint law of derived-allele frequencies $p = (p_1, \dots, p_L)$ is

$$P_{f_w}[p \mid \Theta] = \delta\Big(\prod_{j=1}^{L}(1 - p_j) - f_w\Big)\,\frac{1}{B[\Theta]}\prod_{j=1}^{L}p_j^{\Theta_j - 1}\Big(\sum_{i=1}^{L}p_i\Big)^{-\sum_i\Theta_i}\Big(\sum_{j=1}^{L}\frac{f_w\,p_j}{1 - p_j}\Big),$$

a generalized Dirichlet law on the $(L-1)$-dimensional surface fixed by $f_w$; as $f_w \to 0$ it reduces to the inverted Dirichlet law.

## Proof sketch

For $L = 2$ the inverted Dirichlet law of $x_2 = p_2/p_1$ is the beta-prime density $x^{\Theta_l - 1}(1 + x)^{-2\Theta_l}/B(\Theta_l, \Theta_l)$, symmetric under $x \mapsto 1/x$; conditioning on which locus is major (probability $1/2$ each) folds it onto $[0,1]$ and doubles it. Heuristically, the major locus is the one where the first successful mutation arises, and the minor locus's share is fixed by how long the second successful mutation takes to appear relative to the growth of the first lineage; in Yule time this waiting time is exponential with mean $1/\Theta_l$ for one competing locus. With $L - 1$ competing loci the first of them arrives at total rate $(L-1)\Theta_l = \Theta_{\mathrm{bg}}$, which is why the two-locus formula applies after rescaling. Selection strength cancels because both mutation input and lineage splitting scale with $s_b$.

## Depends on

- [Inverted Dirichlet law of adaptive allele-frequency ratios](inverted-dirichlet-law-of-adaptive-allele-frequency-ratios.md)

## Sources

- I. Höllinger, P. S. Pennings and J. Hermisson, "Polygenic adaptation: From sweeps to subtle frequency shifts", *PLoS Genetics* 15 (2019), e1008035, Equations (8)–(10) and section "Expected allele frequency ratio", <https://doi.org/10.1371/journal.pgen.1008035> (PMC6443195).
