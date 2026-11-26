# Real exponential integral Ei

For real $x \ne 0$, the classical real exponential integral is $\operatorname{Ei}(x) = \gamma + \log|x| + \sum_{n \ge 1} x^n/(n \cdot n!)$, with $\gamma$ the Euler–Mascheroni constant; for $x > 0$ this is $\gamma + \log x + \sum_{n \ge 1} x^n/(n \cdot n!)$. The linked function is total: it uses Mathlib's logarithm, with $\log x = \log|x|$ for $x \ne 0$ and $\log 0 = 0$, so its value at $0$ is $\gamma$, while the classical $\operatorname{Ei}$ has a logarithmic singularity there.
