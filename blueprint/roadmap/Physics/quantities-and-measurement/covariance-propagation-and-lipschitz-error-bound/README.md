# Covariance propagation and Lipschitz error bounds

On a finite sample space with real weights $p$ (a probability distribution when $p \ge 0$ and
$\sum p = 1$), the weighted mean vector and covariance matrix of $AX + b$ are $A\bar X + b$ and
$A\,C\,A^\top$, with $\bar X$ and $C$ those of $X$, when the weights sum to $1$. Nonlinear
first-order propagation $f(x + \delta) \approx f(x) + Df(x)\,\delta$ is an approximation whose
remainder is bounded under second-derivative bounds; a Lipschitz map moves by at most $L\|\delta\|$.
A linear calibration $y = A\theta$ determines $\theta$ exactly when the kernel of $A$ is trivial.

## Weighted means and exact affine covariance propagation

- [Weighted mean vector of $X$ on a finite sample space](mean-vec.md)
- [Coordinates of the weighted mean vector are weighted sums](mean-vec-apply.md)
- [For weights summing to 1, the mean vector of $AX + b$ is $A\bar X + b$](mean-vec-affine.md)
- [For weights summing to 1, $AX + b$ has covariance matrix $A C A^\top$](cov-matrix-affine.md)
- [Weighted variance of $a_1X_1 + a_2X_2$ with the covariance cross term](cov-matrix-two-linear.md)
- [With zero covariance, weighted variances of $a_1X_1$ and $a_2X_2$ add](variance-linear-two-uncorrelated.md)

## First-order remainder bounds for Jacobian propagation

- [$C^2$ Taylor bound $H\delta^2/2$ when $-H\le f''\le H$ on an interval](taylor-first-order-bound.md)
- [First-order remainder $f(x+\delta) - f(x) - Df(x)\,\delta$](jacobian-remainder.md)
- [Unit-step segment bound $H_i$ gives remainder bound $H_i/2$](jacobian-remainder-component-le.md)
- [Scaled segment bound gives remainder bound $H_i\Vert\delta\Vert^2/2$](jacobian-remainder-component-le-of-scale.md)
- [Box Hessian bound gives remainder bound $H_i\Vert\delta\Vert^2/2$](jacobian-remainder-component-le-of-hessi.md)

## Deterministic Lipschitz error bounds

- [Lipschitz error bound: output error at most $L$ times the input error](lipschitz-error-propagation.md)
- [Lipschitz error budget: output error at most $L$ times the input bound](lipschitz-error-budget.md)
- [For $x \mapsto Ax + b$ the output error is exactly $A\delta$](affine-exact.md)

## Identifiability of a linear calibration model

- [Identifiability of a linear calibration model $y = A\theta$](identifiable.md)
- [A calibration matrix is identifiable iff its kernel is trivial](identifiable-iff-trivial-ker.md)
- [With a nonzero kernel vector, $A\theta$ never determines $\theta$](exists-distinct-of-nontrivial-ker.md)
- [With fewer observations than parameters, $A$ is not identifiable](not-identifiable-of-lt.md)
- [For identifiable $A$ the normal matrix $A^\top A$ is injective](identifiable-normal-injective.md)
- [For identifiable $A$ the normal equations have at most one solution](normal-equations-unique.md)

## Identifiability on an affine parameter space

- [Identifiability of $A$ on an affine parameter space $S$](identifiable-on-affine.md)
- [Identifiability on $\theta_0 + V$ via differences from $\theta_0$](identifiable-on-affine-mk.md)
- [Identifiable on $\theta_0 + V$ iff $\ker A \cap V = \{0\}$](identifiable-on-affine-mk-iff-trivial-ke.md)
- [An identifiable matrix is identifiable on every affine parameter space](identifiable-on-affine-of-identifiable.md)
- [On the whole space, affine identifiability is identifiability](identifiable-on-affine-top-iff-identifia.md)
- [The product $AP$ is identifiable iff $A(P\xi) = 0$ forces $\xi = 0$](identifiable-mul-basis-iff-trivial-ker.md)
- [Basis matrix $P$ of $V$: identifiable on $\theta_0 + V$ iff $AP$ is](identifiable-on-affine-mk-iff-identifiab.md)
- [A nonzero kernel vector in $V$ defeats uniqueness on $\theta_0 + V$](exists-distinct-on-affine-of-nontrivial.md)
