# Law of total expectation

On a finite measure space, let $X$ be a measurable random variable with values in a finite set with measurable singletons and $f$ an integrable real function. Then $\int f\, d\mu = \sum_x \mu(X = x)\, \mathbb{E}[f \mid X = x]$, where $\mathbb{E}[f \mid X = x]$ is the integral of $f$ against $\mu$ conditioned on $\{X = x\}$ (the zero measure, hence integral $0$, when that event is null).
