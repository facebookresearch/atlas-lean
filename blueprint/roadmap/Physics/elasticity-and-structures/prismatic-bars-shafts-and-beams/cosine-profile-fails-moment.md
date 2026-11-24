# A cosine profile meets the clamped conditions but not zero tip moment

Let $EI > 0$ and $L > 0$, and let $w(x) = 1 - \cos(2\pi x/L)$, a clamped-clamped profile. Then

$$w(0) = 0, \qquad w'(0) = 0, \qquad EI\, w''(L) \ne 0,$$

indeed $w''(L) = (2\pi/L)^2$. So $w$ meets the two clamped conditions at $x = 0$ but violates the
free-end moment condition $EI\, w''(L) = 0$ of the
[clamped-free cantilever problem](is-cantilever-solution.md), which is a finite clamped-free
problem, not a periodic one.
