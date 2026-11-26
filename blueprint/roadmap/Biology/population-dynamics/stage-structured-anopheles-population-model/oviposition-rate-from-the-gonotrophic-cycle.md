# Oviposition rate from the gonotrophic cycle

**Setting.** An adult female mosquito dies at constant per-capita rate $\mu_M > 0$ (exponential lifespan with mean $1/\mu_M$) and, while alive, lays $\varepsilon$ viable eggs at the end of each gonotrophic cycle of fixed length $\delta > 0$, i.e. at ages $\delta, 2\delta, 3\delta, \dots$. Define the population-level daily oviposition rate $\beta$ as the expected number of eggs laid in a lifetime divided by the expected lifetime.

**Proposition.**

1. The proportion of females surviving $j$ gonotrophic cycles is $p^j$ with $p = e^{-\mu_M \delta}$, and the expected lifetime egg output is

$$\varepsilon \sum_{j \ge 1} p^j = \frac{\varepsilon\, p}{1 - p} = \frac{\varepsilon}{e^{\mu_M \delta} - 1}.$$

2. Hence

$$\beta = \frac{\varepsilon\, \mu_M}{e^{\mu_M \delta} - 1} \le \beta_{\max} = \frac{\varepsilon_{\max}\, \mu_M}{e^{\mu_M \delta} - 1},$$

where $\varepsilon_{\max}$ is the maximum batch size; $\beta < \beta_{\max}$ when some eggs are laid in unsuitable sites or fail to hatch.
3. $\beta \to \varepsilon/\delta$ as $\mu_M \delta \to 0$, and $\beta$ is decreasing in $\mu_M$ for fixed $\varepsilon, \delta$.

## Expansion

Survival to age $j\delta$ under constant hazard is $e^{-\mu_M j \delta}$, and summing the geometric series gives (1); dividing by the mean lifetime $1/\mu_M$ gives (2). For (3), $x/(e^{x}-1) \to 1$ as $x \to 0$ and $x \mapsto x/(e^{x} - 1)$ is decreasing on $(0,\infty)$. With $\varepsilon_{\max} = 93.6$ eggs, $\delta = 3$ days and $\mu_M \approx 0.096$ per day the bound is $\beta_{\max} \approx 27$ eggs per female per day, consistent with the posterior median $\beta \approx 21$ fitted to Garki entomological data. Individual females oviposit periodically, but a population of asynchronous females lays at an approximately constant rate, which is what allows $\beta$ to enter an ordinary differential equation.

## Sources

- M. T. White, J. T. Griffin, T. S. Churcher, N. M. Ferguson, M.-G. Basáñez, A. C. Ghani, "Modelling the impact of vector control interventions on *Anopheles gambiae* population dynamics", Parasites & Vectors 4 (2011) 153, Methods, "Oviposition", Eqs. (2)–(3), and Table 1, <https://doi.org/10.1186/1756-3305-4-153> (PMC3158753).
