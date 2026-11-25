# The Volterra-form sub-conjecture of Scottish Book Problem 124 holds

For every continuous
function $f : \mathbb{R} \to \mathbb{R}$ with $f(0) \ne 0$ and every function
$y : \mathbb{R} \to \mathbb{R}$ that is Lebesgue integrable on $[0, 1]$, if
$\int_0^x y(t) f(x - t)\,dt = 0$ for every $x \in [0, 1]$, then $y = 0$ almost everywhere on
$[0, 1]$.

## Sources

- Józef Marcinkiewicz, Problem 124 of the Scottish Book; typescript PDF p.58, printed p.55. Typescript typo, corrected: the typescript prints the equation as $\int_0^1 y(t) f(x - t)\, dt = 0$, but the intended upper limit is $x$ (Volterra form). The literal reading with $\int_0^1$ is false: $f \equiv 1$, $y(t) = t - 1/2$ is a nonzero solution. Only the Volterra reading, with $\int_0^x$, is stated here. Positive by the local Titchmarsh convolution theorem: E. C. Titchmarsh, "The zeros of certain integral functions", Proc. London Math. Soc. s2-25 (1926), 283–302, DOI 10.1112/plms/s2-25.1.283. Sketch: Titchmarsh gives $\lambda, \mu \ge 0$ with $\lambda + \mu \ge 1$ such that $y = 0$ a.e. on $(0, \lambda)$ and $f = 0$ a.e. on $(0, \mu)$. Continuity of $f$ at $0$ with $f(0) \ne 0$ forces $\mu = 0$ (otherwise $f$ would be a.e. zero on a positive-measure initial interval while being nonzero near $0$), so $\lambda \ge 1$ and $y = 0$ a.e. on $[0, 1]$.
