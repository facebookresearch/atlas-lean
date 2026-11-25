# Reversible additive noise models satisfy the identifiability differential equation

**Reversible additive noise models satisfy the identifiability differential equation**
(Peters, Mooij, Janzing and Schölkopf, *Causal discovery with continuous additive noise models*,
JMLR 15 (2014), equation (7), Condition 19 and the proof of Theorem 20 in Appendix A.5, after
Hoyer et al. 2009). Let $f, g, \nu, \xi, \tilde\nu, \eta : \mathbb{R} \to \mathbb{R}$ be three
times continuously differentiable, where $\nu, \xi$ are the log-densities of the noise and of the
cause of the model $Y = f(X) + N$ and $\tilde\nu, \eta$ those of a backward model
$X = g(Y) + \tilde N$, and suppose both models give the same joint log-density,
$\nu(y - f(x)) + \xi(x) = \tilde\nu(x - g(y)) + \eta(y)$ for all $x, y$. Then at every point
$(x, y)$ with $\nu''(y - f(x)) f'(x) \ne 0$,

$$\xi''' = \xi'' \left(-\frac{\nu''' f'}{\nu''} + \frac{f''}{f'}\right) - 2 \nu'' f'' f' + \nu' f''' + \frac{\nu' \nu''' f'' f'}{\nu''} - \frac{\nu' (f'')^2}{f'},$$

where $\nu$ and its derivatives are evaluated at $y - f(x)$ and $\xi$, $f$ and their derivatives
at $x$.

Condition 19 of Peters et al. calls the triple $(f, p_X, p_N)$ identifiable when it does *not* satisfy this equation at all points where $\nu''(y - f(x)) f'(x) \neq 0$; the statement here is the core of the proof of Theorem 20: a model satisfying Condition 19 has no backward additive noise model with three times continuously differentiable ingredients. For fixed $f$ and noise law, if there is a $y_0$ with $\nu''(y_0 - f(x)) f'(x) \neq 0$ for all but countably many $x$, the laws of $X$ violating Condition 19 lie in a three-dimensional family (their Proposition 21), so nonlinear additive noise models are generically identifiable. For Gaussian $X$ and $N$ the equation forces $f$ to be linear (their Corollary 22), the reversible case of the [linear Gaussian model](exists-indep-fun-backward-of-has-gaussia.md).
