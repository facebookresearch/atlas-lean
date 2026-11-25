# Integral snd map nonresponse Shift

Let $P$ be a finite measure on $\{0,1\} \times \mathbb R$ (points $(r, y)$, $r = 1$ for response) under which the outcome $y$ is integrable, let $\delta \in \mathbb R$, and let $s_\delta$ be the $\delta$-shift of nonrespondents, $s_\delta(r, y) = (r, y)$ if $r = 1$ and $s_\delta(r, y) = (r, y + \delta)$ if $r = 0$. Then the shift moves the full-data mean by $\delta$ times the nonresponse probability:

$$\int y \, d(P \circ s_\delta^{-1}) = \int y \, dP + \delta\, P(r = 0).$$
