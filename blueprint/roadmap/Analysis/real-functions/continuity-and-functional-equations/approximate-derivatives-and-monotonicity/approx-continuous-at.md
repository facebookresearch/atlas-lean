# Approximate continuity

A function $f\colon\mathbb R\to\mathbb R$ is approximately continuous at $x$ if, for every
$\varepsilon>0$, the exceptional set
$B_\varepsilon=\{y:|f(y)-f(x)|\ge\varepsilon\}$ has density zero at $x$:

$$
\lim_{\delta\to0^+}\frac{\lambda^*(B_\varepsilon\cap(x-\delta,x+\delta))}{2\delta}=0,
$$

where $\lambda^*$ is Lebesgue outer measure. For a Lebesgue-measurable function this is equivalent
to the good set $\{y:|f(y)-f(x)|<\varepsilon\}$ having density one. For arbitrary functions the
latter condition with outer measure is weaker: a set and its complement can both have full
outer measure in an interval.

## Sources

- K. Beanland, P. Humke, and T. Richards, [“On Scottish Book Problem 157”](https://doi.org/10.14321/realanalexch.41.2.0331), *Real Analysis Exchange* 41(2) (2016), 331–346.
- [Counterexample to the good-set outer-measure condition](https://github.com/facebookresearch/atlas-lean/issues/8429).
