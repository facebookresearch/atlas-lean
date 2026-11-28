# Mean imputation is not identification, in general

Full-data laws are measures on $\{0,1\} \times \mathbb R$, a point $(r, y)$ recording the response indicator $r$ ($r = 1$ for a respondent) and the outcome $y$. The observed data of $(r, y)$ are $o(r, y) = (r, y)$ if $r = 1$ and $o(r, y) = (0, 0)$ if $r = 0$; the observed-data law of $P$ is the pushforward $P \circ o^{-1}$. Let $P$ be a probability measure on $\{0,1\} \times \mathbb R$ with $y$ integrable, $P(r = 0) \ne 0$ and $P(r = 1) \ne 0$. Then there is a probability measure $Q$ on $\{0,1\} \times \mathbb R$ with $y$ integrable, the same observed-data law $Q \circ o^{-1} = P \circ o^{-1}$, $Q(r = 1) \ne 0$, and respondents' mean different from its full-data mean:

$$\frac{\int_{\{r = 1\}} y \, dQ}{Q(r = 1)} \ne \int y \, dQ.$$
