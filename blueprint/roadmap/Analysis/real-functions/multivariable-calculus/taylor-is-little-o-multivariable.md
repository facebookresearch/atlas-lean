# Taylor's theorem with little-o remainder in several variables

Let $E$ and $F$ be normed
vector spaces over $\mathbb{R}$, let $n$ be a natural number, and let $f : E \to F$ be $n$ times
continuously differentiable on a neighbourhood of a point $x_0 \in E$. Write $D^k f(x_0)$ for the
$k$-th Fréchet derivative of $f$ at $x_0$, a continuous $k$-linear map from $E^k$ to $F$. Then, as
$x$ tends to $x_0$,

$$f(x) - \sum_{k=0}^{n} \frac{1}{k!}\, D^k f(x_0)(x - x_0, \ldots, x - x_0) =
o\bigl(\|x - x_0\|^n\bigr).$$

## Sources

- The integral-remainder form exists as `map_add_eq_sum_add_integral_iteratedFDeriv`.
- H. Cartan, *Differential Calculus*, Ch. III, Taylor's formula with remainder.
- https://en.wikipedia.org/wiki/Taylor%27s_theorem#Taylor's_theorem_in_several_variables
