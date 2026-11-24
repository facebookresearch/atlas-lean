# Projections of a fluctuation path are driving functionals

Let $\beta, \gamma \ge 0$, $T \ge 0$, $t \in [0, T]$ and $x$ continuous on $[0, T]$. For
$\omega \in \Omega$, let $M(\omega)$ be a path continuous on $[0, T]$, let
$Z(\omega) = (U_0(\omega), M(\omega)|_{[0, T]})$, an element of
$\mathbb{R}^2 \times C([0, T], \mathbb{R}^2)$, and let $U(\omega)$ be a
[fluctuation path](is-fluctuation-path.md) driven by $M(\omega)$ from $U_0(\omega)$ around $x$. For
every $\ell \in \mathbb{R}^2$ there are $y$, continuous on $[0, t]$ with $y(t) = \ell$ and
$y'(s) = -DF(x(s))^{\mathsf T} y(s)$ on $(0, t)$, and a
[continuous linear functional](exists-driving-functional.md) $\Lambda$ on
$\mathbb{R}^2 \times C([0, T], \mathbb{R}^2)$ with

$$
\Lambda(u, f) = \langle y(0), u \rangle + \langle \ell, f(t) - f(0) \rangle +
\int_0^t \bigl\langle DF(x(s))^{\mathsf T} y(s), f(s) - f(0) \bigr\rangle\, ds,
$$

such that $\langle \ell, U(\omega)(t) \rangle = \Lambda(Z(\omega))$ for every $\omega$.
