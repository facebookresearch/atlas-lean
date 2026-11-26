# Influences of a monotone Boolean function

If $f : \{-1, 1\}^n \to \{-1, 1\}$ is monotone ($f(x) \le f(y)$ whenever $x \le y$
coordinatewise), then for every coordinate $i$,

$$\mathrm{Inf}_i[f] = \hat f(\{i\}).$$

For monotone $f$ the derivative $D_i f$ is the $0$-$1$ indicator that $i$ is pivotal, so
$\mathrm{Inf}_i[f] = \mathbb{E}[D_i f] = \hat f(\{i\})$.

## Sources

- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014 (arXiv:2105.10386), Proposition 2.21.
