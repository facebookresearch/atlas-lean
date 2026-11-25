# Pathwise solution of the Langevin equation

For real $\theta, \sigma, x_0$ and a path $w : \mathbb{R} \to \mathbb{R}$, the pathwise solution of the Langevin equation driven
by $w$ is

$$x(t) = e^{-\theta t} x_0 + \sigma \Bigl( w(t) - e^{-\theta t} w(0) - \theta \int_0^t e^{-\theta (t - u)} w(u)\, du \Bigr), \qquad t \in \mathbb{R},$$

an integral of a non-integrable function being read as $0$. For a continuous path $w$ it solves the
Langevin equation $x(t) = x_0 - \theta \int_0^t x(u)\, du + \sigma (w(t) - w(0))$
([statement](ou-path-solution-integral-eq.md)), and by integration by parts it is
$e^{-\theta t} x_0 + \sigma \int_0^t e^{-\theta(t - u)}\, dw(u)$ with a Riemann–Stieltjes integral; for a
Brownian path that integral is an Itô integral. For an arbitrary path neither reading holds: for
$\theta = \sigma = x_0 = 1$, $w(0) = 0$ and $w(u) = 1/u$ for $u > 0$, the integral is read as $0$ and
$x(t) = e^{-t} + 1/t$ for $t > 0$, while the Langevin equation, whose integral is also read as $0$,
would require $x(t) = 1 + 1/t$.
