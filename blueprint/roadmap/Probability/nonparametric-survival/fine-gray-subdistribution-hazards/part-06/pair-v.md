# Information limit of the paired model at a given coefficient

Let $\mu_0$ be a measure on a measurable space $S$, $\iota$ a set of causes with cause of interest $c \in \iota$, and $\varepsilon_a, \varepsilon_b$ two maps from $S$ to $\iota \cup \{\star\}$ ($\star$ meaning censored). Let $p_a$ and $p_b$ be the cause-of-interest event masses $\mu_0(\{\varepsilon_a = c\})$ and $\mu_0(\{\varepsilon_b = c\})$ (see [the cause-of-interest event mass of a status map](pair-prob-a.md)), with infinite measures read as $0$, and $m(b) = e^b/(e^b + 1)$ the [risk-set covariate mean](pair-mean.md). For $\beta_0 \in \mathbb{R}$, the information limit at $\beta_0$ is the nonnegative real number

$$
v = \frac{p_a + p_b}{2}\, m(\beta_0)\bigl(1 - m(\beta_0)\bigr),
$$

the value at $\beta_0$ of the [information limit of the paired design](pair-info-limit.md).
