# Strong-selection invasion probability of a mutant pathogen strain

**Model.** Hosts immigrate at rate $\lambda n$, die naturally at rate $\delta$, and strain $i \in \{1, \dots, d\}$ is transmitted at rate $\beta_i S/N$ per infected host, kills its host at extra rate $\alpha_i$ (virulence) and is cleared at rate $\gamma_i$. As the scale $n \to \infty$, the densities $(\bar S^{(n)}, \bar I^{(n)}_i, \bar N^{(n)})$ converge almost surely, uniformly on compact time intervals, to the solution of

$$\dot S = \lambda - \Bigl(\sum_{i=1}^d \beta_i \frac{I_i}{N} + \delta\Bigr) S, \qquad \dot I_i = \Bigl(\beta_i \frac{S}{N} - (\delta + \alpha_i + \gamma_i)\Bigr) I_i, \qquad \dot N = \lambda - \delta N - \sum_{i=1}^d \alpha_i I_i .$$

Let $R_{0,i} = \beta_i/(\delta + \alpha_i + \gamma_i)$. If $R_{0,1} > R_{0,i}$ for all $i > 1$, $R_{0,1} > 1$ and $\delta > \alpha_1$, the single-strain endemic equilibrium of strain 1 is globally asymptotically stable from every initial state with $I_1(0) > 0$.

**Proposition (strong selection).** Take two strains with $R_{0,2} > R_{0,1}$.

1. If strain 2 starts at a macroscopic density, $\bar I^{(n)}_2(0) \to I_2(0) > 0$, then strain 1 goes extinct with probability tending to 1.
2. If strain 1 is at its endemic equilibrium and strain 2 is introduced in $k$ copies, then for every $\varepsilon > 0$, the probability that strain 1 goes extinct and the system comes within $\varepsilon$ of the strain-2 endemic equilibrium in finite time converges to

$$1 - \left(\frac{R_{0,1}}{R_{0,2}}\right)^{k}.$$

3. (Resident away from equilibrium) If a single strain-2 host enters while strain 1 follows the deterministic single-strain trajectory $(S(t), I_1(t), N(t))$, the extinction probability of strain 2 tends to $q = J/(1+J)$, where

$$J = \int_0^\infty \exp\Bigl(-\int_0^s \Bigl[\beta_2 \frac{S(u)}{N(u)} - (\delta + \alpha_2 + \gamma_2)\Bigr] du\Bigr) (\delta + \alpha_2 + \gamma_2)\, ds,$$

and with $k$ initial copies the fixation probability is asymptotic to $1 - q^k$.

4. (Near equilibrium) For initial data $S^\star + \varepsilon s(0)$, $I_1^\star + \varepsilon i_1(0)$, $N^\star + \varepsilon n(0)$ around the strain-1 equilibrium and $\Lambda = \beta_2 (1/R_{0,1} - 1/R_{0,2})$, the invasion probability of a single mutant is

$$1 - q = 1 - \frac{R_{0,1}}{R_{0,2}} - \varepsilon \Bigl(1 - \frac{R_{0,1}}{R_{0,2}}\Bigr)^{2} K \bigl(R_{0,1} \Lambda s(0) - \Lambda n(0) - (\beta_1 - \alpha_1) i_1(0)\bigr) + O(\varepsilon^2)$$

for an explicit constant $K$ depending on $\beta_1, \beta_2, \alpha_1, \delta, R_{0,1}$ and $\Lambda$. Thus, at equal $R_0$ advantage, perturbations that make the pathogen population grow (more susceptibles, fewer resident infections) favour fast, transmissible strains, and saturated hosts favour slow ones.

## Expansion

Near the resident equilibrium, $S/N \approx 1/R_{0,1}$, so each strain-2 host transmits at rate $\beta_2/R_{0,1}$ and is removed at rate $\delta + \alpha_2 + \gamma_2$: a supercritical linear birth–death process whose extinction probability from $k$ ancestors is $(R_{0,1}/R_{0,2})^k$. Once strain 2 reaches $\varepsilon n$ hosts the law of large numbers takes over and carries the system to the strain-2 equilibrium, where strain 1 is in turn a subcritical birth–death process and dies out, so invasion implies replacement. Away from equilibrium the mutant is a time-inhomogeneous birth–death process in the environment set by the resident, and Kendall's formula for its extinction probability gives $q = J/(1+J)$; expanding the resident trajectory to first order around equilibrium yields the near-equilibrium correction.

## Sources

- Todd Parsons, Amaury Lambert, Troy Day, Sylvain Gandon, "Pathogen evolution: slow and steady spreads the best", arXiv (2017). Main-text strong-selection fixation formula (Section "Results"); Supplementary Proposition 3, Definition 1, Proposition 4, Proposition 5, Theorem 1, Corollary 1, Proposition 6, Proposition 11. <https://doi.org/10.48550/arXiv.1711.09795> Published version: Journal of The Royal Society Interface 15 (2018) 20180135, <https://doi.org/10.1098/rsif.2018.0135>.
