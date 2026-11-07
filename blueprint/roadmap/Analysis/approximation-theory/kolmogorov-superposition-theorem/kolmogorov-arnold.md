# Kolmogorov–Arnold superposition with a single outer function

Let $n \ge 1$ and let
$f : \mathbb{R}^n \to \mathbb{R}$ be continuous on the unit cube $[0, 1]^n$. Then there exist a
continuous function $g : \mathbb{R} \to \mathbb{R}$ and continuous functions
$\varphi_{k,l} : \mathbb{R} \to \mathbb{R}$ for $0 \le k \le 2n$ and $0 \le l < n$ such that for
every $x = (x_0, \dots, x_{n-1}) \in [0, 1]^n$,

$$f(x) = \sum_{k=0}^{2n} g\left(\sum_{l=0}^{n-1} \varphi_{k,l}(x_l)\right).$$

Both $g$ and the $\varphi_{k,l}$ may depend on $f$, so this is weaker than the form in which the
inner functions are universal.

## Sources

- A. N. Kolmogorov, *On the representation of continuous functions of several variables by superposition of continuous functions of one variable and addition*, Doklady Akad. Nauk SSSR 114 (1957), 953-956. V. I. Arnold, *On functions of three variables*, Doklady Akad. Nauk SSSR 114 (1957), 679-681. G. G. Lorentz, *Metric entropy, widths, and superpositions of functions*, Amer. Math. Monthly 69 (1962), 469-485 (single-outer-function refinement). Listed as §80 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `kolmogorov_arnold_superposition`.
