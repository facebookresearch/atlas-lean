# Asymptotics of mean conditional fixation times in the Moran process with constant fitness

**Model.** In the Moran process with population size $N$, types A and B have constant (frequency-independent) fitnesses $r$ and $1$, $r \ne 1$, $r > 0$. In each time step one individual is chosen to reproduce with probability proportional to fitness and its offspring replaces an individual chosen uniformly at random. Let $t_i$ be the mean number of steps to absorption (fixation of either type) from $i$ A individuals, and $t^N_i$, $t^0_i$ the mean absorption times conditioned on fixation of A, respectively of B. The mean conditional fixation time of a single mutant, $t_{\mathrm{fix}} = t^N_1$, is the same for a single A mutant and a single B mutant. Let $\gamma$ be the Euler–Mascheroni constant.

**Theorem (single mutant).** As $N \to \infty$,

$$t_{\mathrm{fix}} = N\,\frac{r+1}{|r-1|}\Big[\log N + \gamma + \log\big(1 - \min(r, r^{-1})\big)\Big] + \frac12\Big(\frac{r+1}{r-1}\Big)^2 + O(1/N).$$

For the unconditional absorption times,

$$t_1 = \frac{r+1}{r}N\log N + \Big[\frac{r+1}{r}\gamma + \log(1 - r^{-1})\Big]N + \frac{1+r^2}{2r(r-1)} + O(1/N)\quad (r>1),$$

$$t_1 = -\frac{\log(1-r)}{r}\,N + \frac{r}{1-r} + O(1/N)\quad (0<r<1).$$

**Theorem (fixed initial fraction).** For fixed rational $x \in (0,1)$ and $r > 1$, with $Nx$ an integer,

$$t^N_{Nx} = \frac{r}{r-1}N\log N + \frac{r}{r-1}N\Big(\gamma + \log(1 - \tfrac1r) + \log(1-x) - \tfrac1r\log x\Big) + \frac{r+1}{2(r-1)^2}\Big(\frac{r}{1-x} + \frac1x - 1\Big) + O(1/N),$$

$$t^0_{Nx} = \frac{1}{r-1}N\log N + \frac{1}{r-1}N\Big(\gamma + \log(1-\tfrac1r) - r\log(1-x) + \log x\Big) + \frac{r(r+1)}{2(r-1)^2}\Big(\frac{1}{1-x} + \frac{1}{rx} - 1\Big) + O(1/N),$$

and $t_{Nx}$ has the same expansion as $t^N_{Nx}$ up to $O(1/N)$ (fixation of the fitter type dominates). The case $0 < r < 1$ follows by exchanging the roles of the types. By contrast, under neutrality $t^N_{Nx} = -\frac{(1-x)\log(1-x)}{x}N^2 - \frac12 N + O(1)$.

## Expansion

The mean times are explicit finite sums over the birth–death chain, built from terms $r^{\pm j}/j$ and $r^{\pm j}/(N-j)$. Their asymptotics follow from sharp estimates such as $\sum_{j=1}^{N-1} r^j/j = \frac{r^N}{N}\big[\frac{1}{r-1} + O(1/N)\big]$ for $r>1$ and $-\log(1-r) + O(r^N/N)$ for $r<1$, together with harmonic-number expansions $H_N = \log N + \gamma + O(1/N)$. Under selection, the process spends $O(N)$ steps near each boundary and crosses the bulk deterministically, giving the $N\log N$ scaling instead of the neutral $N^2$; the $\log N$ coefficient $(r+1)/|r-1|$ is the inverse of the per-step drift near the boundaries.

## Sources

- Rosângela A. Pires and Armando G. M. Neves, "Asymptotic behavior of mean fixation times in the Moran process with frequency-independent fitnesses", J. Math. Biol. 88 (2024), 12, <https://doi.org/10.1007/s00285-023-02032-1>. Numbering follows the arXiv version, arXiv:2212.14748 (2022): Theorems 1–5 and the summation estimates (Theorems 6–9), <https://doi.org/10.48550/arXiv.2212.14748>.
