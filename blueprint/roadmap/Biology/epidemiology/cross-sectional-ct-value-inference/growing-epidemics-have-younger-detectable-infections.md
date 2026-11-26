# Growing epidemics have younger detectable infections

In the setting of the [cross-sectional Ct-value likelihood](cross-sectional-ct-value-likelihood-for-daily-infection-probabilities.md), suppose incidence grew (or declined) exponentially at rate $r \in \mathbb{R}$ over the window preceding the test day, $\pi_{t-a} = \pi_t\, e^{-ra}$ for $a = 1, \dots, A_{\max}$, and that $\phi_a > 0$ for every $a$. The infection age $A$ of a randomly sampled detectable individual then has law

$$q_r(a) \;=\; P(A = a \mid \text{detectable}) \;=\; \frac{\phi_a\, e^{-ra}}{\sum_{b=1}^{A_{\max}} \phi_b\, e^{-rb}}, \qquad a = 1, \dots, A_{\max},$$

which does not depend on $\pi_t$. If $r_1 < r_2$, then $q_{r_2}$ is smaller than $q_{r_1}$ in the likelihood-ratio order: $q_{r_2}(a)/q_{r_1}(a)$ is strictly decreasing in $a$. Consequently $A$ is stochastically smaller under $r_2$, and $\mathbb{E}_{r}[g(A)]$ is nonincreasing in $r$ for every nondecreasing $g$. In particular, if the age-specific Ct law is stochastically increasing in age over the window (viral load declining after its peak), then a faster-growing epidemic produces a cross-section with lower observed Ct values (higher viral loads), and a declining epidemic produces higher ones, with no change in individual-level viral kinetics.

## Depends on

- [Cross-sectional Ct-value likelihood for daily infection probabilities](cross-sectional-ct-value-likelihood-for-daily-infection-probabilities.md)

## Expansion

The displayed law follows from Bayes' rule with prior $\pi_{t-a}$ on ages and likelihood $\phi_a$ of detection; $\pi_t$ cancels. The ratio $q_{r_2}(a)/q_{r_1}(a) = c\, e^{-(r_2 - r_1)a}$ with $c > 0$ independent of $a$ is strictly decreasing, and the likelihood-ratio order implies the usual stochastic order, hence the statement about nondecreasing $g$. Mixing the age-specific Ct laws with weights $q_r$ preserves the order when those laws are themselves stochastically ordered in age. This is the mechanism by which the median and skewness of cross-sectional Ct values track the epidemic growth rate: a rising epidemic has a predominance of recent, high-viral-load infections, while a falling one has more old infections with low viral loads, so that the Ct distribution of a single random cross-section is informative about the growth rate $r$, and hence about the effective reproduction number.

## Sources

- J. A. Hay, L. Kennedy-Shaffer, S. Kanjilal, N. J. Lennon, S. B. Gabriel, M. Lipsitch, M. J. Mina, "Estimating epidemiologic dynamics from cross-sectional viral load distributions", *Science* 373(6552) (2021) eabh0635, Results, "Relationship between observed Ct values and epidemic dynamics", and Materials and methods, "Single cross section model", <https://doi.org/10.1126/science.abh0635> (PMC8527857).
