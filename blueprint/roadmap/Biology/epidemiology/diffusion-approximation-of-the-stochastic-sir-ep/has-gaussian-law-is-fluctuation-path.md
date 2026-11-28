# The limit fluctuation is Gaussian with the limit covariance

Let $\beta, \gamma \ge 0$, let $x$ be continuous on $[0, T]$, and let $V$ be a
[limit covariance](is-limit-covariance.md) around $x$ from $V_0$. Let $P$ be a measure on $\Omega$
and $Z : \Omega \to \mathbb{R}^2 \times C([0, T], \mathbb{R}^2)$ a random element with a Gaussian
law under $P$, for the Borel $\sigma$-algebra of $C([0, T], \mathbb{R}^2)$ (so $P$ is a probability
measure), whose first component is $U_0$ and whose second component is $M$ on $[0, T]$. Write $E$
for integrals against $P$, $\langle a, b \rangle$ for the [dot product](dot.md) and $K$ for the
[integrated diffusion matrix](quad-cov.md). Assume that, for all $a, b \in \mathbb{R}^2$ and
$s, r \in [0, T]$,

- $E\, U_0 = 0$ and $E\,(M(s) - M(0)) = 0$;
- $E\, \langle a, U_0 \rangle \langle b, U_0 \rangle = \langle a, V_0 b \rangle$ and
  $E\, \langle a, U_0 \rangle \langle b, M(s) - M(0) \rangle = 0$;
- $E\, \langle a, M(s) - M(0) \rangle \langle b, M(r) - M(0) \rangle =
  \langle a, K(\min(s, r))\, b \rangle$;

and let $U(\omega)$ be the [fluctuation path](is-fluctuation-path.md) driven by $M(\omega)$ from
$U_0(\omega)$ around $x$, for every $\omega$.

Then for every $t \in [0, T]$, $U(t)$ has a Gaussian law with $E\, U(t) = 0$ and

$$
E\, \langle a, U(t) \rangle \langle b, U(t) \rangle = \langle a, V(t)\, b \rangle
\quad \text{for all } a, b \in \mathbb{R}^2.
$$

The proof writes $\langle \ell, U(t) \rangle$ as the integration-by-parts Wiener integral
$\langle y(0), U_0 \rangle + \int_0^t \langle y(s), dM(s) \rangle$ against the solution of the
adjoint equation $y' = -DF(x)^{\mathsf T} y$, $y(t) = \ell$, a continuous linear functional of $Z$.
