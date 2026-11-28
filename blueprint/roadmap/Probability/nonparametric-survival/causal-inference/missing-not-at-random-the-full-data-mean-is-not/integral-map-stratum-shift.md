# Integral map stratum Shift

Let $\mathcal X$ be a measurable space with measurable singletons. Full-data laws are measures on $\mathcal X \times \{0,1\} \times \mathbb R$, a point $(x, r, y)$ recording an always-observed covariate $x$, the response indicator $r$ ($r = 1$ for a respondent) and the outcome $y$. Let $P$ be a finite measure on $\mathcal X \times \{0,1\} \times \mathbb R$ under which $y$ is integrable, $x_0 \in \mathcal X$, $c \in \mathbb R$, and let $s_{x_0, c}$ be the stratum shift

$$s_{x_0, c}(x, r, y) = \begin{cases} (x, r, y + c) & x = x_0 \text{ and } r = 0, \\ (x, r, y) & \text{otherwise.} \end{cases}$$

Then

$$\int y \, d(P \circ s_{x_0, c}^{-1}) = \int y \, dP + c\, P(x = x_0,\ r = 0).$$
