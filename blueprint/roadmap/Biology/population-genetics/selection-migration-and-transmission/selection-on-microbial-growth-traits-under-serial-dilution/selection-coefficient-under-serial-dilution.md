# Selection coefficient of growth traits under serial dilution

**Model.** Asexual strains $k = 1, \dots, K$ grow in a well-mixed batch culture with initial amount $R > 0$ of a single limiting resource. Strain $k$ has lag time $L_k \ge 0$, exponential growth rate $r_k > 0$ and yield $Y_k > 0$ (cells per unit resource), and these traits are unchanged by competition. At the start of a cycle the total population is $N_0$ and strain $k$ has frequency $x_k$; strain $k$ then has $N_k(t) = N_0 x_k e^{r_k (t - L_k)}$ cells for $t \ge L_k$. Growth stops at the saturation time $t_c$ (assumed larger than every $L_k$) when the resource is used up:

$$\sum_{k} \frac{N_0 x_k \, e^{r_k (t_c - L_k)}}{Y_k} = R.$$

The culture is then diluted by the factor $D > 1$ into fresh medium containing $R$ again, and stationary-phase death is neglected.

**Selection coefficient.** The selection coefficient of strain $i$ against strain $j$ over one cycle is the change in their log-ratio,

$$s_{ij} = \ln\frac{N_i^{\mathrm{final}}}{N_j^{\mathrm{final}}} - \ln\frac{N_i^{\mathrm{initial}}}{N_j^{\mathrm{initial}}} = r_i (t_c - L_i) - r_j (t_c - L_j).$$

**Two strains at fixed dilution factor.** For a mutant (strain 2) against a wild type (strain 1), with relative growth rate $\gamma = (r_2 - r_1)/r_1$ and relative lag $\omega = (L_2 - L_1) r_1$,

$$s \approx \gamma \ln D - \omega,$$

valid when $|\gamma| \ll 1$. The bottleneck size adjusts each cycle to

$$N_0 = \frac{R \bar Y}{D}, \qquad \bar Y = \Bigl(\sum_k \frac{x_k}{Y_k}\Bigr)^{-1},$$

so yield changes alter the bottleneck but do not enter $s$: yield is under no direct selection.

## Remarks

With fixed $D$ the population fold-change over a cycle is exactly $D$, so the wild type grows for a time $t_c - L_1 \approx (\ln D)/r_1$ when the mutant is rare. Substituting into $s_{21} = r_2(t_c - L_2) - r_1(t_c - L_1)$ and expanding to first order in $\gamma$ gives $(r_2 - r_1)(\ln D)/r_1 - r_1(L_2 - L_1)$, which is the stated formula. The growth and lag phases thus contribute additively, and the dilution factor sets their relative weight: a larger $D$ lengthens exponential growth and favors growth-rate mutations over lag mutations. Neutral coexistence ($s = 0$) needs the exact tuning $\gamma \ln D = \omega$. Because the saturation condition fixes $N_0 = R\bar Y / D$, the frequency dependence of $\bar Y$ cancels, in contrast with fixed-$N_0$, variable-$D$ protocols where selection becomes frequency dependent. The ratio $R/D$ sets the bottleneck and hence the strength of drift.

## Sources

- J. Lin, M. Manhart and A. Amir, "Evolution of microbial growth traits under serial dilution", Genetics (2020), <https://doi.org/10.1534/genetics.120.303149>, PMCID PMC7337084. Model section, Equations 1–4.
