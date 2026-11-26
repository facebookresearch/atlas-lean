# The roots of van der Waerden numbers diverge for each fixed color count

Fix a natural $r\ge2$. As the natural progression length $k$ tends to infinity, the reals $(W(r,k):\mathbb R)^{1/k}$ tend to $+\infty$, with $W$ the [van der Waerden forcing number](van-der-waerden-forcing-number.md) and powers interpreted as real powers. This is a full limit at infinity, not a subsequential bound. The source uses totalized real division in the exponent at $k=0$, which does not affect the limit.

## Depends on

- [Van der Waerden forcing number](van-der-waerden-forcing-number.md).

## Proof depends on

- [Uniform superexponential lower bound for van der Waerden numbers](van-der-waerden-uniform-superexponential-lower-bound.md); at fixed $r\ge2$ the positive constant $\lfloor\log_2 r\rfloor/100000$ remains after taking the $k$th root.

## Sources

- OpenAI, [Fixed-color root limit](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/ProgressionColoring/Main.lean#L34-L38) and [Derivation from the quantitative bound](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/ProgressionColoring/GrowthConsequences.lean#L47-L58).
