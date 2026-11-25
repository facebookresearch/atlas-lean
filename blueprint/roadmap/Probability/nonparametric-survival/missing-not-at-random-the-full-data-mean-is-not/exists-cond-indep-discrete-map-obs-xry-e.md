# Positivity failure defeats identification even under MAR

Let $\mathcal X$ be a measurable space with measurable singletons. Full-data laws are measures on $\mathcal X \times \{0,1\} \times \mathbb R$, a point $(x, r, y)$ recording an always-observed covariate $x$, the response indicator $r$ ($r = 1$ for a respondent) and the outcome $y$. The observed data of $(x, r, y)$ are $o(x, r, y) = (x, r, y)$ if $r = 1$ and $(x, 0, 0)$ if $r = 0$. Assume $\mathcal X$ is countable. Let $P$ be a probability measure on $\mathcal X \times \{0,1\} \times \mathbb R$ with $y$ integrable, under which response is missing at random given the covariate: for every measurable $B \subseteq \mathbb R$ and every $w \in \mathcal X$,

$$P(r = 1,\ y \in B,\ x = w)\, P(x = w) = P(r = 1,\ x = w)\, P(y \in B,\ x = w).$$

Suppose some stratum $x_0$ has positive probability, $P(x = x_0) \ne 0$, but no respondents, $P(r = 1,\ x = x_0) = 0$. Then for every $t \in \mathbb R$ there is a probability measure $Q$ on $\mathcal X \times \{0,1\} \times \mathbb R$ with $y$ integrable, satisfying the same missing-at-random condition, with the same observed-data law $Q \circ o^{-1} = P \circ o^{-1}$, and with

$$\int y \, dQ = t.$$

So a failure of positivity defeats identification of the mean even under missingness at random.
