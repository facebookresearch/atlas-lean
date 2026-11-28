# Threshold and final size for SIR epidemics on households embedded in a configuration network

**Model.** A population of $m$ households, a fraction $\rho_n$ of which have size $n$ (mean size $\mu_H = \sum_n n\rho_n < \infty$), is overlaid by a configuration-model network of global contacts with degree law $D$, $P(D = k) = p_k$, mean $\mu_D$ and variance $\sigma_D^2$. Infectives have i.i.d. infectious periods $I$ with Laplace transform $\phi_I(\theta) = E[e^{-\theta I}]$; during $I$ an infective contacts each household member at rate $\lambda_L$ and each global neighbour at rate $\lambda_G$ (Poisson processes). Let $p_G = 1 - \phi_I(\lambda_G)$ be the probability of transmission to a given global neighbour, $\tilde\rho_n = n\rho_n/\mu_H$ the size-biased household-size law, $\tilde D$ the size-biased degree, $P(\tilde D = k) = kp_k/\mu_D$, and $\mu^{(n)}(\lambda_L)$ the mean number of other members infected in a single-household epidemic in a household of size $n$ started by one infective.

**Threshold.** As $m \to \infty$ the infected households form, early on, a branching process; it is supercritical iff $R_* > 1$, where

$$R_* = p_G\Big(\mu_{\tilde D - 1} + \mu_D \sum_{n \ge 1} \tilde\rho_n\, \mu^{(n)}(\lambda_L)\Big), \qquad \mu_{\tilde D - 1} = \mu_D + \frac{\sigma_D^2}{\mu_D} - 1 .$$

**Major outbreak probability.** With $C$, $\tilde C$ the offspring numbers of the initial and of a typical later household, $p_{\mathrm{maj}} = 1 - f_C(\sigma)$, where $\sigma$ is the smallest root in $[0,1]$ of $f_{\tilde C}(s) = s$ ($f_X$ denotes a probability generating function).

**Final size.** Let $M^{(n)}$ be the size, excluding the focal individual, of its local (within-household) susceptibility set. The susceptibility set of a random individual is approximated by a branching process with

$$f_B(s) = \sum_n \tilde\rho_n f_D(1 - p_G + p_G s)\, f_{M^{(n)}}\big(f_D(1 - p_G + p_G s)\big), \quad f_{\tilde B}(s) = \sum_n \tilde\rho_n f_{\tilde D - 1}(1 - p_G + p_G s)\, f_{M^{(n)}}\big(f_D(1 - p_G + p_G s)\big).$$

Then $E[\tilde B] = E[\tilde C]$, and if $R_* > 1$ the fraction of the population infected by a major outbreak converges in probability to $z = 1 - f_B(\xi)$, with $\xi$ the smallest root of $f_{\tilde B}(s) = s$ in $[0,1]$.

## Expansion

A household reached through a global edge has a primary case with $\tilde D - 1$ free global edges, each transmitting with probability $p_G$; the $\mu^{(n)}$ secondary cases it generates locally each carry a fresh degree $D$. Size-biasing by $n$ appears because a globally contacted individual lands in a household of size $n$ with probability $\tilde\rho_n$. The forward process (who can I infect) and the backward process (who could infect me) have different offspring laws but the same mean, so they share the threshold; the extinction probability of the backward process gives the probability that a given individual escapes a major outbreak, hence the final size. Reducing to $\mu^{(n)} \equiv 0$ recovers the configuration-model threshold $p_G\,\mu_{\tilde D - 1}$, and $D \equiv 0$ the households-only model.

## Sources

- F. Ball, D. Sirl, "Evaluation of vaccination strategies for SIR epidemics on random networks incorporating household structure", Journal of Mathematical Biology 76 (2018) 483–530, Sect. 2.1–2.2, equations (2.1)–(2.7), <https://doi.org/10.1007/s00285-017-1139-0>, PMCID: PMC5754546.
