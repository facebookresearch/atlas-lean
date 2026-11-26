# Binomial test for infected cells under ambient contamination

**Ambient profile.** For an array (or droplet batch) $a$, barcodes with very few transcripts (fewer than $50$) are treated as empty, and the proportion of their transcripts assigned to gene $g$ gives the ambient profile $P^{(a)}$ with $0 < P^{(a)}_g < 1$ and $\sum_g P^{(a)}_g = 1$. The viral share of ambient RNA is $E^{(a)} = \sum_{g \in \text{viral genes}} P^{(a)}_g$.

**Contamination fraction.** Given nonnegative gene-expression programs $G_1,\dots,G_K$ learned by non-negative matrix factorization, append $P^{(a)}$ and normalize every program to unit $L_1$ norm, giving $\tilde G_1,\dots,\tilde G_{K+1}$. For cell $c$ with count vector $X_c$, solve the non-negative least-squares problem

$$\min_{U_{c1},\dots,U_{c,K+1} \ge 0}\ \Bigl\|X_c - \sum_{k=1}^{K+1} U_{ck}\tilde G_k\Bigr\|_2^2,$$

and set the ambient fraction $A_c = U_{c,K+1}/\sum_k U_{ck}$.

**Test.** If cell $c$ has $N_c$ transcripts and contains no virus, its viral count is modelled as $\mathrm{Binomial}(N_c,\ E^{(a)}A_c)$. For a false-positive level $f$, let $T_c$ be the upper-$f$ quantile of this law (the inverse survival function at $f$); call the cell infected when its viral count exceeds $T_c$. Then, under the null model, $P(\text{call} \mid \text{uninfected}) \le f$ for every cell.

**Sensitivity.** If a fraction $p_{\mathrm{cell}}$ of an infected cell's own transcripts are viral, its viral count is modelled as $B_1 + B_2$ with independent $B_1 \sim \mathrm{Binomial}(N_c - N_{\mathrm{amb}}, p_{\mathrm{cell}})$ and $B_2 \sim \mathrm{Binomial}(N_{\mathrm{amb}}, E^{(a)}A_c)$, $N_{\mathrm{amb}} = \lceil N_cA_c\rceil$, and the per-cell sensitivity is $P(B_1 + B_2 > T_c)$, computed by convolving the two laws.

## Expansion

Thresholds adapt to each cell: a deeply sequenced or heavily contaminated cell needs more viral reads to be called, so ambient viral RNA released by lysed cells does not make every cell in a high-viremia sample look infected. Spiked-in cells of a species that the virus does not infect act as an empirical negative control for the calibration. Averaging the sensitivity over sampled $(N_c, A_c)$ pairs across a range of $f$ traces a receiver operating characteristic for the detection of cells with, for example, $1\%$ or $0.1\%$ viral transcripts.

## Sources

- D. Kotliar, A. E. Lin, J. Logue et al., "Single-cell profiling of Ebola virus disease in vivo reveals viral and host dynamics", Cell (2020), STAR Methods ("Detection of EBOV infected cells" and "Estimation of the infection receiver operator characteristic"), <https://doi.org/10.1016/j.cell.2020.10.002>.
