# Duality identity for fluctuation paths

Let $x$ and $m$ be continuous on $[0, T]$, let $U$ be a [fluctuation path](is-fluctuation-path.md):
$U$ is continuous on $[0, T]$ and $U(t) = u_0 + (m(t) - m(0)) + \int_0^t DF(x(s))\, U(s)\, ds$ for
$t \in [0, T]$, and let $t \in [0, T]$. If $y$ is continuous on $[0, t]$ and
$y'(s) = -DF(x(s))^{\mathsf T} y(s)$ for $s \in (0, t)$, then

$$
\langle y(t), U(t) \rangle = \langle y(0), u_0 \rangle + \langle y(t), m(t) - m(0) \rangle +
\int_0^t \bigl\langle DF(x(s))^{\mathsf T} y(s), m(s) - m(0) \bigr\rangle\, ds,
$$

with the [dot product](dot.md). The last two terms are $\int_0^t \langle y(s), dm(s) \rangle$
integrated by parts: the Wiener integral in integration-by-parts form.
