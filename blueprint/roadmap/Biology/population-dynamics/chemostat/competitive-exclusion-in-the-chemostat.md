# Competitive exclusion in the chemostat

For $N$ species competing for one nutrient in a chemostat with a common removal rate $D > 0$ and input concentration $S_{in} > 0$, $\dot s = D(S_{in} - s) - \sum_{i=1}^N \mu_i(s) x_i$ and $\dot x_i = (\mu_i(s) - D) x_i$ (yields normalized to $1$), assume each growth rate $\mu_i$ is $C^1$, increasing, with $\mu_i(0) = 0$, and let the break-even concentration $\lambda_i$ solve $\mu_i(\lambda_i) = D$ ($\lambda_i = \infty$ if there is no solution). If the species are labelled so that $\lambda_1 < \lambda_2 < \dots < \lambda_N$ and $\lambda_1 < S_{in}$, then every solution with nonnegative initial condition and $x_1(0) > 0$ converges to $(s, x_1, x_2, \dots, x_N) = (\lambda_1, S_{in} - \lambda_1, 0, \dots, 0)$: the species with the lowest break-even concentration excludes the others (Rapaport and Veruete, Proposition 1). Any species with $\lambda_j \ge S_{in}$ dies out whatever the initial condition (their Lemma 1(2)). For Monod growth $\mu_i(s) = m_i s/(a_i + s)$, $\lambda_i = a_i D/(m_i - D)$ when $m_i > D$; this case is the theorem of Hsu, Hubbell and Waltman (1977).

## Depends on

- [Global dynamics of the single-species chemostat](../../../Biology/population-dynamics/chemostat/global-dynamics-of-the-single-species-chemostat.md)

## Expansion

1. The model, with break-even concentrations as in the [single-species chemostat](../../../Biology/population-dynamics/chemostat/global-dynamics-of-the-single-species-chemostat.md).
2. The conservation relaxation $s + \sum_i x_i \to S_{in}$ and the persistence of total biomass when $\lambda_1 < S_{in}$ (Lemma 1).
3. The inductive comparison argument of Rapaport and Veruete on the proportions of species $n, n - 1, \dots, 2$, and the Lyapunov-function proof of Hsu, Hubbell and Waltman for Monod rates.
4. Extinction of species that cannot grow at $S_{in}$, and ties $\lambda_i = \lambda_j$ (Section 3.5 of the source), as separate statements.

## Sources

- A. Rapaport and M. Veruete, A new proof of the competitive exclusion principle in the chemostat, Discrete Contin. Dyn. Syst. Ser. B 24 (2019), 3755–3764, Section 2, Assumptions 1–2, Proposition 1, Lemma 1, Section 3. <https://doi.org/10.3934/dcdsb.2018314>
- Original result: S. B. Hsu, S. Hubbell and P. Waltman, A mathematical theory for single-nutrient competition in continuous cultures of micro-organisms, SIAM J. Appl. Math. 32 (1977), 366–383. <https://doi.org/10.1137/0132030> The Monod case follows Rapaport and Veruete (2019), who attribute the first proof to this paper.
