# Clonal growth rates from serial cancer cell fractions

Let a circulating tumor population be sampled at times $t_1 < \dots < t_m$ (measured from the start of a therapy at $t = 0$). At each time let $c_k(t_j) \in [0, 1]$ be the [cancer cell fraction](../cancer-cell-fraction-estimation/ccf-mle.md) of subclone $k$, estimated from sequencing after correcting allelic fractions for purity and local copy number, and let $A(t_j)$ be the absolute tumor-cell count per unit volume (for leukemia, the absolute lymphocyte count) and $V$ the total volume (for blood, about 5 L). The **clone size** is

$$N_k(t_j) = c_k(t_j)\, A(t_j)\, V.$$

Assume each clone grows or declines exponentially at a constant net rate $r_k$ during therapy, $N_k(t) = N_k(0)\, e^{r_k t}$. Then $\ln N_k(t_j) = \ln N_k(0) + r_k t_j$, and

- with exactly two measurements, $\hat r_k = \dfrac{\ln N_k(t_2) - \ln N_k(t_1)}{t_2 - t_1}$;
- with $m > 2$ measurements, $\hat r_k$ is the least-squares slope of $\ln N_k(t_j)$ on $t_j$, with its usual standard error;
- the size of a resistant clone at treatment start is back-extrapolated as $\hat N_k(0) = N_k(t_1)\, e^{-\hat r_k t_1}$, and its doubling or halving time is $\ln 2 / |\hat r_k|$.

Uncertainty in $\hat r_k$ and $\hat N_k(0)$ is propagated by drawing $c_k(t_j)$ from their posterior distributions.

## Depends on

- [Maximum-likelihood cancer cell fraction](../cancer-cell-fraction-estimation/ccf-mle.md)

## Expansion

Converting fractions to absolute numbers matters: a clone whose fraction rises while the total burden falls may still be shrinking, so growth must be read from $N_k$, not $c_k$. Under the exponential model the log-sizes are linear in time, so ordinary regression applies, and a constant rate extrapolated back from relapse estimates how many resistant cells were present before therapy, i.e. whether resistance was pre-existing. In patients with chronic lymphocytic leukemia relapsing on the BTK inhibitor ibrutinib, subclones carrying BTK or PLCG2 mutations, or del(8p), expanded with positive rates while the sensitive bulk declined, and back-extrapolated sizes, together with droplet-microfluidic detection, indicated that rare resistant subclones were already present before treatment.

## Sources

- J. A. Burger, D. A. Landau, A. Taylor-Weiner, I. Bozic, H. Zhang, K. Sarosiek et al., "Clonal evolution in patients with chronic lymphocytic leukaemia developing resistance to BTK inhibition", Nature Communications (2016), 11589, Methods "ABSOLUTE analysis and clonal evolution mapping" and "Mathematical analysis of clonal kinetics", <https://doi.org/10.1038/ncomms11589>, PMCID PMC4876453.
