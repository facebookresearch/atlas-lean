# Johari–Tsitsiklis characterization of smooth market-clearing mechanisms

A smooth market-clearing mechanism allocates a divisible resource via a differentiable demand function $D(\rho, \theta)$ and the unique price $\rho > 0$ with $\sum_r D(\rho, \theta_r) = C$. Among the regular mechanisms of this class (whose price-anticipating payoffs are concave for all admissible utilities and whose demand functions cover $[0, \infty)$), every mechanism that guarantees competitive equilibria to be socially optimal and Nash equilibria to exist uniquely achieves worst-case efficiency at most $3/4$ at Nash equilibrium, with equality if and only if it is equivalent to proportional sharing $D(\rho, \theta) = \theta / \rho$ up to a price scaling.

## Proof sketch

Concavity for all admissible utilities forces the demand function to be of the power form $\theta \rho^{-1/c}$ up to reparametrization; the efficiency of the power-elasticity mechanisms is computed explicitly and maximized at $c = 1$, which is proportional sharing.

## Depends on

- [Kelly's proportional allocation mechanism](kellys-proportional-allocation-mechanism.md)

## Proof depends on

- [Johari–Tsitsiklis 3/4 efficiency of the Kelly mechanism](johari-tsitsiklis-3-4-efficiency-of-the-kelly-mechanism.md)
- [Kelly competitive equilibria exist and are socially optimal](kelly-competitive-equilibria-exist-and-are-socially-optimal.md)

## Sources

- Ramesh Johari, "The Price of Anarchy and the Design of Scalable Resource Allocation Mechanisms", Algorithmic Game Theory, Cambridge University Press, 2007.
- Ramesh Johari and John N. Tsitsiklis, "Efficiency of Scalar-Parameterized Mechanisms", Operations Research, 2009.
