# Weak-selection fixation probability of a mutant pathogen strain

**Setting.** In the multi-strain stochastic SIR model with host immigration rate $\lambda n$, natural death rate $\delta$, and strain-specific transmission $\beta_i$, virulence $\alpha_i$ and clearance $\gamma_i$, suppose the strains are nearly neutral in the sense that

$$R^{(n)}_{0,i} = \frac{\beta_i}{\delta + \alpha_i + \gamma_i} = R_0^\star \Bigl(1 + \frac{r_i}{n}\Bigr) + o\Bigl(\frac{1}{n}\Bigr), \qquad i = 1, \dots, m,$$

so the deterministic limit has a set $\Omega$ of coexistence equilibria (a curve for two strains) rather than a single stable equilibrium.

**Theorem (diffusion on the coexistence set).** Speed time up by $n$. The rescaled process converges weakly to a diffusion that lives on $\Omega$ and is determined by the infected densities alone: for $i = 1, \dots, m$,

$$d\hat I_i = s_i(\hat{\mathbf{I}})\, \hat I_i\, dt + \frac{1}{\sqrt{R_0^\star}} \sum_{k=1}^m \Bigl( \mathbf{1}_{\{i=k\}} - \frac{(\beta_k - \alpha_k) \beta_i \hat I_i}{\sum_{j=1}^m (\beta_j - \alpha_j) \beta_j \hat I_j} \Bigr) \sqrt{2 \beta_k \hat I_k}\, dB_k ,$$

where the drift $s_i$ is built from the selection coefficients $r_i$ and the projection onto $\Omega$. For two strains, the frequency $P$ of strain 2 is a one-dimensional diffusion with drift $b(p)$ and variance $a(p)$, and its fixation probability from $P(0) = p$ is

$$h(p) = \frac{\int_0^p \exp\bigl(-2 \int^q \frac{b(u)}{a(u)}\, du\bigr)\, dq}{\int_0^1 \exp\bigl(-2 \int^q \frac{b(u)}{a(u)}\, du\bigr)\, dq}.$$

**Small-difference approximation.** Write $\beta_2 = \beta_1 (1 + \sigma)$ and $\alpha_2 = \alpha_1(1+\theta)$ with $\sigma, \theta$ small, and let $I_e(0)$ be the resident equilibrium infected density. To first order in $\sigma, \theta$,

$$h(p) = p + \frac{1}{2}\Bigl( \frac{\beta_1 - \beta_2}{\beta_2} + \Bigl(1 - \frac{R^{(n)}_{0,1}}{R^{(n)}_{0,2}}\Bigr) n I_e(0) \Bigr) p (1-p),$$

and for a single mutant host ($p = 1/(n I_e(0))$) the fixation probability is approximately

$$\frac{1}{n I_e(0)} + \frac{1}{2}\Bigl( \frac{1}{n I_e(0)} \frac{\beta_1 - \beta_2}{\beta_2} + 1 - \frac{R^{(n)}_{0,1}}{R^{(n)}_{0,2}} \Bigr).$$

Hence with equal $R_0$ a strain with **lower** transmission (and correspondingly lower virulence) has a fixation advantage of order $1/(n I_e(0))$: in small pathogen populations, slow and steady strains are favoured, and strains with lower $R_0$ can fix, while in large populations the $R_0$ difference dominates.

## Proof depends on

- [Strong-selection invasion probability of a mutant pathogen strain](strong-selection-fixation-of-a-mutant-pathogen-strain.md)

## Expansion

When $R_0$ values differ only by $O(1/n)$, the law of large numbers drives the process quickly onto the coexistence set $\Omega$, after which the demographic noise and the weak selection act on the slow time scale $nt$. A projection argument for stochastic processes near an attracting set of fixed points gives the limiting diffusion on $\Omega$, with noise projected along $\Omega$. A frequency process then follows from Itô's formula, and the fixation probability solves the boundary value problem $\mathcal{L} h = 0$, $h(0) = 0$, $h(1) = 1$ for its generator. Expanding to first order gives the neutral term $p$ plus a selection term from the $R_0$ difference (scaled by pathogen population size) and from the transmission difference $\sigma$, which acts through differences in the variance of offspring numbers. This weak-selection result matches the strong-selection formula $1 - (R_{0,1}/R_{0,2})^k$ at intermediate scales.

## Sources

- Todd Parsons, Amaury Lambert, Troy Day, Sylvain Gandon, "Pathogen evolution: slow and steady spreads the best", arXiv (2017). Main-text weak-selection fixation approximation (Section "Results"); Supplementary Definition 1, Proposition 7, Proposition 10 and the two-strain fixation-probability formulas in the weak-selection section. <https://doi.org/10.48550/arXiv.1711.09795> Published version: Journal of The Royal Society Interface 15 (2018) 20180135, <https://doi.org/10.1098/rsif.2018.0135>.
