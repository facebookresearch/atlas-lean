# Map obs XRY map stratum Shift

Let $\mathcal X$ be a measurable space with measurable singletons. Full-data laws are measures on $\mathcal X \times \{0,1\} \times \mathbb R$, a point $(x, r, y)$ recording an always-observed covariate $x$, the response indicator $r$ ($r = 1$ for a respondent) and the outcome $y$. The observed data of $(x, r, y)$ are $o(x, r, y) = (x, r, y)$ if $r = 1$ and $(x, 0, 0)$ if $r = 0$. For $x_0 \in \mathcal X$ and $c \in \mathbb R$ let $s_{x_0, c}$ be the stratum shift

$$s_{x_0, c}(x, r, y) = \begin{cases} (x, r, y + c) & x = x_0 \text{ and } r = 0, \\ (x, r, y) & \text{otherwise.} \end{cases}$$

Then for every measure $P$ on $\mathcal X \times \{0,1\} \times \mathbb R$,

$$(P \circ s_{x_0, c}^{-1}) \circ o^{-1} = P \circ o^{-1}.$$
