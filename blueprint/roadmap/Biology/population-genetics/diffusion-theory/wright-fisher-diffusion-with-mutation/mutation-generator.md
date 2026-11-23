# Wright–Fisher generator with two-way mutation

For real numbers $\theta_1$ and $\theta_2$, a real function $f$ and a real number $x$, let

$$(L_{\theta_1,\theta_2} f)(x) = \frac{x(1 - x)}{2}\, f''(x) + \frac{\theta_1(1 - x) - \theta_2 x}{2}\, f'(x),$$

where a derivative that does not exist is taken to be $0$. For $\theta_1, \theta_2 \ge 0$, $x \in [0, 1]$ and twice-differentiable $f$, it is the backward generator of the Wright–Fisher diffusion with two-way mutation, applied to $f$, with time in units of $2N$ generations and scaled mutation rates $\theta_1 = 4Nu_1$ towards the allele and $\theta_2 = 4Nu_2$ away from it.

## Sources

- W. J. Ewens, *Mathematical Population Genetics I: Theoretical Introduction*, 2nd ed., Springer (2004).
