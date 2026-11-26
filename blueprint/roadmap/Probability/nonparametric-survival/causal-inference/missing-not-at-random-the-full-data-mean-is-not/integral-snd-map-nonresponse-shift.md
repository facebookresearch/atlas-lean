# Shifting nonrespondents' outcomes moves the outcome integral

Let $P$ be a finite measure on $\{0,1\} \times \mathbb R$ (points $(r, y)$, $r = 1$ for response) under which the outcome $y$ is integrable, let $\delta \in \mathbb R$, and let $s_\delta$ be the $\delta$-shift of nonrespondents, $s_\delta(r, y) = (r, y)$ if $r = 1$ and $s_\delta(r, y) = (r, y + \delta)$ if $r = 0$. Then the shift moves the outcome integral by $\delta$ times the nonresponse mass:

$$\int y \, d(P \circ s_\delta^{-1}) = \int y \, dP + \delta\, P(r = 0).$$

When $P$ is a probability measure, this says that the shift moves the full-data mean by $\delta$ times the nonresponse probability. For a general finite measure the integral is not a mean: under twice the point mass at a nonrespondent with outcome $0$, the shift by $1$ moves the integral by $2$ and the mean by $1$.
