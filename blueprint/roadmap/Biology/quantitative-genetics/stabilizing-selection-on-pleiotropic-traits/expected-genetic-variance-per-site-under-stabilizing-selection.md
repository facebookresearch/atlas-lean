# Expected genetic variance per site under pleiotropic stabilizing selection

In the model of [allelic dynamics under pleiotropic stabilizing selection](allelic-dynamics-under-pleiotropic-stabilizing-selection.md) with isotropic mutation, the expected contribution of a site with scaled selection coefficient $S=2Ns$ to the additive genetic variance of a focal trait (monomorphic sites counted as $0$) factorises as

$$\mathbb E\big(2a_1^2pq\mid S\big)=\mathbb E(a_1^2\mid S)\,\mathbb E(2pq\mid S)=\frac{w^2}{2Nn}\,S\,\mathbb E(2pq\mid S),$$

and the expected total variance is this per-site expectation times the population mutation input $2NU$. Pleiotropy therefore enters only as the constant factor $1/n$, which is not identifiable separately from $w$. In the strong-selection regime ($S\gtrsim30$) the decrease of heterozygosity with $S$ cancels the increase of $\mathbb E(a_1^2\mid S)$, and the per-site contribution approaches the constant

$$v_S=\frac{2w^2}{nN},$$

independent of $S$; for effectively neutral sites ($S\lesssim1$) it is $\tfrac12 S\,v_S$. In between, the underdominant dynamics make the contribution reach $v_S$ near $S\approx3$, peak about $30\%$ above $v_S$ near $S\approx10$, and decline slowly to $v_S$.

## Proof sketch

Given $S$, the allele's effect direction and its frequency trajectory are independent, which gives the factorisation, and $\mathbb E(a_1^2\mid s)=w^2s/n$ with $s=S/(2N)$ gives the prefactor. The strong-selection plateau is equivalent to $\mathbb E(2pq\mid S)\approx 4/S$: selection holds a strongly selected allele near loss, so its expected heterozygosity is of order $1/S$ and its variance $a_1^2\cdot 2pq$ is of order $(w^2S/(2Nn))\cdot(4/S)$. Hence intermediate and strongly selected sites contribute similar variance per site but at very different allele frequencies, from common to extremely rare, while nearly neutral sites contribute little. This explains why GWAS discoveries capture a small fraction of heritability and why the architecture is dominated by many sites with small per-site variance.

## Depends on

- [Allelic dynamics under pleiotropic stabilizing selection](allelic-dynamics-under-pleiotropic-stabilizing-selection.md)
- [Effect sizes given selection in Fisher's geometric model](effect-sizes-given-selection-in-fisher-s-geometric-model.md)

## Sources

- Y. B. Simons, K. Bullaughey, R. R. Hudson, G. Sella, "A population genetic interpretation of GWAS findings for human quantitative traits", PLoS Biol. 16 (2018) e2002985, section "Expected variance per site", Equation (12) and Fig. 2A, <https://doi.org/10.1371/journal.pbio.2002985>, PMCID PMC5871013.
