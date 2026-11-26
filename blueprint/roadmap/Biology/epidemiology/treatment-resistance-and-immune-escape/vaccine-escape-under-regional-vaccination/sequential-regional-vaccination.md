# Sequential regional vaccination and the reduction of infections during a campaign

Divide a population into $K$ identical regions, a fraction $C \ll 1$ of each person's contacts being outside their region, and let the total vaccination capacity be $v$ (fraction of the population per unit time), enough to bring the whole population to the target coverage in time $T$. Compare

- **uniform vaccination**: every region is vaccinated at rate $v_k(t) = v$ for $t \in [0, T]$;
- **sequential (spatial) vaccination**: region $k$ is vaccinated at rate $v_k(t) = K v$ for $t \in [t_{k-1}, t_k]$ and not at all otherwise, with $t_k = kT/K$.

Assume adaptive social distancing keeps each region's wild-type infection stream at a constant rate $h$ until that region reaches herd immunity at the end of its own vaccination, after which its infections stop (cross-region infection neglected). Then infections during the campaign total $hT$ under uniform vaccination and

$$hT \cdot \frac{1}{K} \sum_{k=1}^{K} \frac{k}{K} = hT\, \frac{K+1}{2K}$$

under sequential vaccination, a fraction $(K+1)/(2K)$ that decreases to $1/2$ as $K \to \infty$. The campaign ends at the same time $T$ in both regimes.

## Proof sketch

Region $k$ is infected on $[0, kT/K]$, so the average region stops being infected halfway through the campaign. The same mechanism lowers the risk of vaccine escape. A vaccine-resistant variant has a selective advantage only where vaccine coverage is high while wild-type infections, its source, continue, and sequential vaccination replaces one long window in which both hold with $K$ short regional windows. Herd immunity requires coverage at least $1 - 1/R_0$, so the benefit disappears when that coverage cannot be reached: with unvaccinated fractions above about $1/R_0$, leaky vaccines, or fast waning. The coupling $C$ matters only across the moving border between vaccinated and unvaccinated regions. If mobility fluxes decay with distance like $d^{-2}$ and $\bar\rho$ is the typical distance traveled per infection cycle, then $C(\rho) \approx (\bar\rho/\rho)^2$, so regions of radius $\rho \approx \bar\rho/\sqrt{C}$, about $10\,\bar\rho$ for $C = 1\%$, keep coupling low. In simulations the benefit saturates near $K \approx 20$ and is lost for $C > 5\%$.

## Sources

- X. Zhang, G. Lobinska, M. Feldman, E. Dekel, M. A. Nowak, Y. Pilpel, Y. Pauzner, B. Barzel and A. Pauzner, "A spatial vaccination strategy to reduce the risk of vaccine-resistant variants", PLoS Computational Biology 18 (2022) e1010391, Section 2A ("Reducing the total number of infections"), Section 2B ("Estimating C", Figure 5), Section 2E, and Section 3 ("SIR model with regions and mutations"), <https://doi.org/10.1371/journal.pcbi.1010391>, PMCID: PMC9394842.
