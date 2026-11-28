# Cond Indep Discrete map stratum Shift

Let $\mathcal X$ be a measurable space with measurable singletons. Full-data laws are measures on $\mathcal X \times \{0,1\} \times \mathbb R$, a point $(x, r, y)$ recording an always-observed covariate $x$, the response indicator $r$ ($r = 1$ for a respondent) and the outcome $y$. Let $P$ be a measure on $\mathcal X \times \{0,1\} \times \mathbb R$ under which response is missing at random given the covariate: for every measurable $B \subseteq \mathbb R$ and every $w \in \mathcal X$,

$$P(r = 1,\ y \in B,\ x = w)\, P(x = w) = P(r = 1,\ x = w)\, P(y \in B,\ x = w).$$

Each factor is the real number $P(\cdot)$ when it is finite and $0$ when it is infinite; the condition for $P \circ s_{x_0, c}^{-1}$ is read the same way.

Let $x_0 \in \mathcal X$ be a stratum with no respondents, $P(r = 1,\ x = x_0) = 0$, and let $c \in \mathbb R$. Then the pushforward $P \circ s_{x_0, c}^{-1}$ under the stratum shift

$$s_{x_0, c}(x, r, y) = \begin{cases} (x, r, y + c) & x = x_0 \text{ and } r = 0, \\ (x, r, y) & \text{otherwise.} \end{cases}$$

again satisfies the same missing-at-random condition.
