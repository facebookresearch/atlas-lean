# Recursive least squares

Recursive least squares (RLS) estimates the parameter $\theta \in \mathbb{R}^d$ of the linear regression
$y_{k+1} = \varphi_k^\top \theta + w_{k+1}$ from the regressors $\varphi_k$ and the observations $y_{k+1}$, updating
an estimate $\theta_k$ and a matrix $P_k$ at each step. In system identification and adaptive control the regressor
$\varphi_k$ collects past outputs and inputs, and the inputs are themselves computed from the estimates, so the data are
generated in closed loop and are neither independent nor stationary; the theory of Chen and Guo (*Identification and
Stochastic Adaptive Control*, Birkhäuser 1991) and of Lai and Wei (Ann. Statist. 10 (1982)) is built for this setting.

The pages below show that the recursion computes the regularised batch least-squares estimate (the matrix inversion
lemma), identify it with ridge regression when started at $\theta_0 = 0$, $P_0 = \lambda^{-1} I$, and give convergence
in the noise-free case once the smallest eigenvalue of $\sum_k \varphi_k \varphi_k^\top$ tends to infinity. The
stochastic convergence rate $|\theta_{t+1} - \theta|^2 = O(\log r_t / \lambda_{\min}(t))$ under martingale-difference
noise, on the event $\sum_k |\varphi_k|^2 = \infty$ (no persistent excitation is assumed), and the logarithmic regret of the least-squares adaptive predictor are stated
as well.

## The algorithm

- [One step of recursive least squares](rls-step.md)
- [Recursive least-squares estimates](rls.md)
- [Information matrix of recursive least squares](rls-information.md)
- [The information matrix is positive definite](pos-def-rls-information.md)

## Recursive least squares is batch least squares

- [The RLS matrix is the inverse of the information matrix](rls-snd-eq-inv.md)
- [RLS solves the regularised normal equations](rls-information-mul-vec-rls-fst.md)
- [Recursive least squares equals batch regularised least squares](rls-fst-eq.md)
- [Design matrix of the first $t$ regressors](design-matrix.md)
- [Recursive least squares started at $\theta_0 = 0$, $P_0 = \lambda^{-1} I$ is ridge regression](rls-fst-eq-ridge-estimate.md)
- [The RLS estimate minimises the ridge objective](ridge-le-rls-fst.md)

## Convergence

- [Logarithmic bound on the accumulated RLS gains](sum-rls-gain-le-log-det.md)
- [Error identity of noise-free RLS](rls-information-mul-vec-error-of-noise-f.md)
- [Error bound of noise-free RLS under excitation](rls-error-sq-le.md)
- [Convergence of noise-free RLS under growing excitation](tendsto-rls-fst-of-noise-free.md)
- [Convergence rate of recursive least squares under martingale-difference noise](rls-error-sq-le-log-div-lambda-min.md)
- [Logarithmic regret of the least-squares adaptive predictor](rls-regret-sum-le-log.md)

## Shared stochastic energy estimate for recursive least squares

- [Joint stochastic energy and prediction-error bound for recursive least squares](rls-energy-add-half-sum-le-log.md)

## Related topics

- [Least squares, ridge and lasso regression](../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/README.md): the batch problem that the recursion solves; its ridge closed form is used by the identification with ridge regression.
- [Linear least squares](../../../LinearAlgebra/matrix-decompositions/linear-least-squares/README.md): the same normal equations solved by matrix factorisations instead of rank-one updates.
- [Kalman filter](../../../ComputerScience/machine-learning/probabilistic-graphical-models/kalman-filter/README.md): RLS is the Kalman filter for the constant state $\theta_{k+1} = \theta_k$ observed through $y_{k+1} = \varphi_k^\top \theta_k + v_{k+1}$ with unit noise variance, $P_k$ playing the role of the covariance.
- [Linear quadratic regulator](../../../ComputerScience/machine-learning/reinforcement-learning/linear-quadratic-regulator/README.md): Recht's dynamic programming pages; adaptive linear-quadratic control combines least-squares estimates of the system with the Riccati feedback by certainty equivalence.
- [Optimality of stationary policies](../../../ComputerScience/heuristic-search-and-planning/optimality-of-stationary-policies/README.md): Bertsekas's dynamic programming, the optimisation side of feedback design when the model is known.
- [Martingales and optional stopping](../../../Probability/martingales/README.md): the martingale convergence and estimation theorems on which the stochastic convergence theory rests.
- [Capability and limits of feedback](../capability-and-limits-of-feedback/README.md): what feedback, adaptive or not, can achieve for uncertain systems.
- [Pole placement](../pole-placement/README.md): Coron's stabilisation of known linear systems by state feedback, the problem adaptive control solves when the system is unknown.
