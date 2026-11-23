# Generator of the ancestral selection graph line-counting process

For a real number $\sigma$, a real function $f$ on the natural numbers and a natural number $n$, let

$$(A_\sigma f)(n) = n\sigma\bigl(f(n + 1) - f(n)\bigr) + \binom{n}{2}\bigl(f(n - 1) - f(n)\bigr),$$

where $n - 1$ is read as $0$ when $n = 0$. For $\sigma \ge 0$ it is the generator of the line-counting process of the ancestral selection graph with scaled selection coefficient $\sigma$, with branching from $n$ to $n + 1$ lines at rate $n\sigma$ and coalescence from $n$ to $n - 1$ at rate $\binom{n}{2}$, time in units of $2N$ generations.

## Sources

- S. M. Krone and C. Neuhauser, *Ancestral processes with selection*, Theoret. Population Biol. 51 (1997), 210–237.
