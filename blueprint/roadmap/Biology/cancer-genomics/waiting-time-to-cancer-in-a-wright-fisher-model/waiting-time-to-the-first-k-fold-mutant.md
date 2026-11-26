# Expected waiting time to the first k-fold mutant

In the [driver-accumulation Wright–Fisher model](driver-accumulation-wright-fisher-model.md) with $s > 0$, $u d \ll s$ and large $N$, the distribution of error classes is approximately a Gaussian with mean $vt$ and constant variance $\sigma^2$, travelling with speed $v = s\sigma^2$ classes per generation. For constant population size $N$ the speed is approximately

$$v \approx \frac{2 s \log N}{\big(\log \frac{s}{ud}\big)^2},$$

so the expected waiting time until the first cell with $k$ driver mutations appears is

$$t_k \approx \frac{k \big(\log \frac{s}{ud}\big)^2}{2 s \log N}.$$

For a population growing exponentially from $N_{\mathrm{init}}$ to $N_{\mathrm{fin}}$, the waiting time equals that of a constant population of size $N = \sqrt{N_{\mathrm{init}} N_{\mathrm{fin}}}$ (the geometric mean), giving

$$t_k \approx \frac{k \big(\log \frac{s}{ud}\big)^2}{s \log (N_{\mathrm{init}} N_{\mathrm{fin}})}. \qquad (1)$$

Consequences: $t_k$ is linear in $k$, decreases roughly as $1/s$, and depends only logarithmically on the mutation rate $u$, the number of susceptible genes $d$ and the population size. With $d = 100$, $k = 20$, $u = 10^{-7}$ per gene per division and $s = 0.01$, cancer arises within 5–15 years in an adenoma of $10^7$–$10^9$ cells.

## Depends on

- [Driver-accumulation Wright–Fisher model](driver-accumulation-wright-fisher-model.md)

## Expansion

A deterministic replicator limit ($N \to \infty$) is misleading: it gives Poisson class frequencies with parameter $\lambda = ud(e^{st}-1)/s$, whose variance grows without bound, because high-fitness multiple mutants are generated instantly. The approximation instead decouples mutation and selection. Fisher's fundamental theorem gives $v = s\sigma^2$ for a Gaussian wave under multiplicative fitness. To fix $\sigma^2$, consider an initially exponentially growing subpopulation of $j$-fold mutants (growth rate about $s$ relative to the mean) and compute the expected time until it produces its first $(j+1)$-fold mutant; requiring this time to equal $1/v$, the time to advance one class, yields the formula for $v$ above. In a growing population the speed is approximately the average of the speeds at $N_{\mathrm{init}}$ and $N_{\mathrm{fin}}$; since $v$ is proportional to $\log N$, this average is the speed at the geometric mean, and $2 \log \sqrt{N_{\mathrm{init}} N_{\mathrm{fin}}} = \log(N_{\mathrm{init}} N_{\mathrm{fin}})$ gives Eq. (1). The approximation matches Wright–Fisher simulations whenever $s > 0$.

## Sources

- N. Beerenwinkel, T. Antal, D. Dingli, A. Traulsen, K. W. Kinzler, V. E. Velculescu, B. Vogelstein and M. A. Nowak, "Genetic progression and the waiting time to cancer", PLoS Computational Biology 3(11) (2007), e225, Results and Methods ("Analytical approximation", Equation 1), <https://doi.org/10.1371/journal.pcbi.0030225>, PMCID: PMC2065895.
