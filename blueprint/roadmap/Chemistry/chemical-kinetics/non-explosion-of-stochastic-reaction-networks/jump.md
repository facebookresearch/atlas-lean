# State after one firing of a reaction

Let $N$ be a [stochastic chemical reaction network](stochastic-crn.md) on a set $S$ of species
with reactions indexed by a set $\rho$ (any sets). For a reaction $r$ and a state
$x \in \mathbb{N}^S$, the state after $r$ fires at $x$ is $x - \mathrm{src}(r) + \mathrm{prod}(r)$,
computed coordinatewise with natural-number subtraction truncated at $0$:

$$\bigl(x - \mathrm{src}(r) + \mathrm{prod}(r)\bigr)_s
= \max\bigl(x_s - \mathrm{src}(r)_s,\ 0\bigr) + \mathrm{prod}(r)_s \qquad (s \in S).$$

It is the ordinary vector $x - \mathrm{src}(r) + \mathrm{prod}(r)$ when $\mathrm{src}(r) \le x$
coordinatewise, the only case in which the propensity $\lambda_r(x)$ can be nonzero.
