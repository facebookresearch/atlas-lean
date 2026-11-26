# Lower bound on the mean offspring of an outbreak dataset

Consider an outbreak started by a single index case, with transmission chains fully reconstructed. List the cases in order of generation (the index case first, then all second-generation cases, then all third-generation cases, and so on, in any order within a generation), and let $x_i$ be the number of secondary cases infected by the $i$-th listed case. For $n \ge 1$, if the outbreak has at least $n$ cases, then

$$\sum_{i=1}^{n} x_i \ge n - 1, \qquad\text{so}\qquad \hat m_n = \frac{1}{n}\sum_{i=1}^{n} x_i \ge \frac{n - 1}{n},$$

with equality if and only if the outbreak has exactly $n$ cases.

## Expansion

Each case $j \in \{2, \dots, n\}$ has an infector in a strictly earlier generation, and the listing puts every case of an earlier generation before $j$; so the infectors of cases $2, \dots, n$ lie among the first $n$ cases, and these $n - 1$ distinct infections all count towards $\sum_{i \le n} x_i$. If the outbreak has a case $n + 1$, its infector also belongs to a generation before that of case $n + 1$, hence lies among the first $n$, and the sum is at least $n$. If the outbreak has exactly $n$ cases, the first $n$ cases infect exactly cases $2, \dots, n$, and equality holds.

Outbreak datasets are collected only from outbreaks that reached $n$ cases. When the true mean $m$ (the basic reproduction number) is below or near $1$, the bound forces $\hat m_n$ close to or above $1$ however small $m$ is, and superspreading in the last generation pushes it higher. In simulations with $m = 0.5$, the median $\hat m_n$ exceeded $1$ for every sample size reported, while the estimates of the dispersion $k$ from the same outbreak datasets were not biased downward.

## Sources

- J. O. Lloyd-Smith, "Maximum likelihood estimation of the negative binomial dispersion parameter for highly overdispersed data, with applications to infectious diseases", PLoS ONE 2(2) (2007) e180, Methods section 2.1.4, Results section 3.4, and Discussion (minimum value of the sample mean of an outbreak dataset), <https://doi.org/10.1371/journal.pone.0000180> (PMC1791715).
