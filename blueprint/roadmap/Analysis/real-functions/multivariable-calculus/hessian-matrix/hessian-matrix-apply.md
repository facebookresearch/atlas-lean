# Entries of the Hessian matrix

For $f : \mathbb{R}^n \to \mathbb{R}$, a point
$x \in \mathbb{R}^n$ and indices $i, j$, the $(i, j)$ entry of the Hessian matrix of $f$ at $x$ is
$\frac{d}{ds}\big|_{s=0} \frac{d}{dt}\big|_{t=0} f(x + s e_i + t e_j)$, where $e_1, \dots, e_n$ is
the standard basis of $\mathbb{R}^n$ and a derivative that does not exist is taken to be $0$:
differentiate first along $e_j$, then along $e_i$.

## Sources

- `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` / `Differential calculus`, entry `Hessian matrix` (unmapped); W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9.
