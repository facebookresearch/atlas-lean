# Taylor variance bound for moment closure

Let $Y$ be a random vector with values in a convex set $C \subseteq \mathbb{R}^k$ and let $f : C \to \mathbb{R}$ have a continuous Hessian $f''$ whose spectral radius satisfies $\rho(f''(x)) \le b$ on $C$. Then

$$ \mathbb{E}[f(Y)] = f(\mathbb{E}[Y]) + h \sum_{i=1}^k \mathrm{Var}[Y_i] \qquad \text{for some } |h| \le \frac{b}{2} . $$

In a moment hierarchy for a Markov process this replaces $\mathbb{E}[m(X)]$, for a drift-type function $m$, by $m(\mathbb{E}X)$ plus a bounded multiple of the total variance, so the first-moment and summed-second-moment equations close into an ODE system with bounded, possibly time-dependent, coefficients $h(t)$.

## Expansion

Apply the scalar Taylor theorem with Lagrange remainder along the segment from $\mathbb{E}[Y]$ to $Y$: $f(Y) = f(\mathbb{E}Y) + f'(\mathbb{E}Y)^{\top}(Y - \mathbb{E}Y) + \tfrac12 (Y-\mathbb{E}Y)^{\top} f''(\tilde Y)(Y-\mathbb{E}Y)$. Taking expectations kills the linear term, and the quadratic form is bounded by $b\,\|Y - \mathbb{E}Y\|^2$ pointwise. For the SIS model with infection rate $\beta x(1-x)$ and recovery rate $\gamma x$ on the scaled state $x \in [0,1]$, the drift is quadratic and the bound is exact with $h = -\beta$.

## Sources

- B. Armbruster, "A simple and general proof for the convergence of Markov processes to their mean-field limits", arXiv:1602.05224 (2016), Section 2, Lemma 2, and Section 3.1 (SIS example). <https://doi.org/10.48550/arXiv.1602.05224>
