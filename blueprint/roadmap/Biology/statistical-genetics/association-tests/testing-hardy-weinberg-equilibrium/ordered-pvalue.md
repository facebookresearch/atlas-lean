# Ordered p-value of an outcome

For real functions $f, g : \mathbb{N} \to \mathbb{R}$, a bound $M \in \mathbb{N}$ and an outcome
$h \in \mathbb{N}$, the ordered p-value of $h$ is the $f$-mass of the outcomes $j < M$ at least as
extreme as $h$, where $j$ is at least as extreme as $h$ when $g(j) \le g(h)$:

$$\mathrm{pv}_{f, g, M}(h) = \sum_{j < M,\ g(j) \le g(h)} f(j).$$

It is defined for all real $f$ and $g$; it is a probability when $f$ is a probability mass function
on $\{0, \dots, M - 1\}$.
