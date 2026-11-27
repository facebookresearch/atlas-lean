# Tumour burden under exponentially decaying radiation kill

Let a tumour of size $x(t) > 0$ grow exponentially at net rate $p_1 > 0$ and be killed by a permanently implanted radioactive source whose dose rate decays exponentially with decay constant $\lambda > 0$ (for iodine-125, half-life $59.4$ days, so $\lambda = \ln 2 / 59.4\ \mathrm{day}^{-1}$). With radiation kill coefficient $s_1 \ge 0$ and no immune response, the tumour obeys

$$\frac{dx}{dt} = \left(p_1 - s_1 e^{-\lambda t}\right) x, \qquad x(0) = x_0 > 0, \qquad t \ge 0 .$$

Its unique solution is

$$x(t) = x_0 \exp\!\left(p_1 t - \frac{s_1}{\lambda}\left(1 - e^{-\lambda t}\right)\right).$$

Consequently:

1. $\log x$ is convex on $[0,\infty)$, strictly convex when $s_1 > 0$, because $\frac{d^2}{dt^2}\log x = s_1 \lambda e^{-\lambda t} \ge 0$.
2. If $s_1 \le p_1$ the tumour never shrinks. If $s_1 > p_1$ it shrinks on $[0, t^\ast)$ and regrows on $(t^\ast, \infty)$, where $t^\ast = \lambda^{-1} \log(s_1/p_1)$; its minimum is $x(t^\ast) = x_0 \exp\!\big(p_1 t^\ast - (s_1 - p_1)/\lambda\big)$.
3. In particular $x$ has no interior local maximum: under radiation alone the tumour can only fall and then rise, never rise and then fall.
4. The total log-kill delivered by the source is finite, $\int_0^\infty s_1 e^{-\lambda t}\,dt = s_1/\lambda$, so $x(t) e^{-p_1 t} \to x_0 e^{-s_1/\lambda}$ as $t \to \infty$ and any tumour with $p_1 > 0$ eventually regrows without another mechanism of control.

## Proof depends on

- [Global existence and uniqueness for homogeneous linear ODEs](../../../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/exists-unique-has-deriv-at-eq-continuous.md)

## Proof sketch

The equation is linear with time-dependent rate $g(t) = p_1 - s_1 e^{-\lambda t}$, so $x(t) = x_0 \exp \int_0^t g$. The rate $g$ is nondecreasing, which is the convexity of $\log x$; a convex function decreases then increases, with its minimum at the unique zero $t^\ast$ of $g$ when $s_1 > p_1$. Because the implanted seeds are sealed and do not leave the tumour, the dose rate is exactly the decay law of the isotope and $\lambda$ is not a free parameter. Yamamoto et al. use this term as the radiation part of their tumour equation (their Equation 1a) and note that the isotope has lost about $98\%$ of its activity by the time marker bounces are seen, one to two years after implantation.

## Sources

- Y. Yamamoto et al., "Tumour and immune cell dynamics explain the PSA bounce after prostate cancer brachytherapy", British Journal of Cancer (2016), <https://doi.org/10.1038/bjc.2016.171> (PMC4947697), Materials and methods, "Mathematical modelling", Equation (1a).
