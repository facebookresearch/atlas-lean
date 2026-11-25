# Approximate derivative test for monotonicity (Scottish Book Problem 157)

Let $f\colon\mathbb R\to\mathbb R$ be [approximately continuous](approx-continuous-at.md) at every
point, and suppose that at every $x$ the
[upper right-hand approximate derivative](has-positive-upper-right-approx-deriv.md) of $f$ is
positive. Then $f$ is monotone nondecreasing.

Here approximate continuity requires the sets where $|f(y)-f(x)|\ge\varepsilon$ to have density
zero at $x$ for every $\varepsilon>0$. For arbitrary functions it is not enough for the good sets
to have relative outer measure tending to one; [there is a counterexample](https://github.com/facebookresearch/atlas-lean/issues/8429)
to the monotonicity conclusion with that weaker condition.

## Sources

- A. J. (Gus) Ward, Problem 157 of the Scottish Book; solved affirmatively by D. Ornstein,
  “A characterization of monotone functions,” *Illinois Journal of Mathematics* 15 (1971), 73–76,
  and by R. O'Malley (1975), whose theorem on approximate maxima yields a positive solution.
  See K. Beanland, P. Humke, and T. Richards,
  [“On Scottish Book Problem 157”](https://doi.org/10.14321/realanalexch.41.2.0331),
  *Real Analysis Exchange* 41(2) (2016), 331–346.
