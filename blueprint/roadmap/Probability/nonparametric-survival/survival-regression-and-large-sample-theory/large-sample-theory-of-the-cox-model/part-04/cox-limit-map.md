# Limit map of the Cox root

At $(\theta, \beta_0)$, the limit map is $v^{-1}\partial\Psi(\theta, \beta_0)/\partial\mu$ with $v = -\partial\Psi(\theta, \beta_0)/\partial b$ the limiting information; if $v = 0$ the map is $0$ ($0^{-1} = 0$). Each derivative is read as $0$ at points where $\Psi$ is not differentiable (as Mathlib's `deriv` and `fderiv` are), which can happen since $\Psi$ is defined on every real coordinate vector and a risk sum can vanish.
