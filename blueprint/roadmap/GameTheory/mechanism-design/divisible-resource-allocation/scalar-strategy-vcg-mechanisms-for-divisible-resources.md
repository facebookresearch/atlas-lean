# Scalar-strategy VCG mechanisms for divisible resources

Fix a single-parameter family of strictly concave admissible surrogate utilities $U(\cdot\,; \theta)$, $\theta > 0$, whose marginal utilities cover $(0, \infty)$. The scalar-strategy VCG mechanism allocates the feasible $d(\theta)$ maximizing $\sum_i U(d_i; \theta_i)$ and charges Clarke-pivot payments. A bid profile is a Nash equilibrium iff for every user $i$ the allocation maximizes $U_i(x_i) + \sum_{j \ne i} U(x_j; \theta_j)$; for admissible utilities an efficient Nash equilibrium exists (price of stability $1$), inefficient equilibria can also exist (already for two users with $U(x) = \log(1 + x)$), and if every user's true utility $U_i$ is concave, strictly increasing, continuous on $[0, \infty)$ and differentiable on $(0, \infty)$ with $U_i'(0^+) = \infty$ (so $U_i$ lies outside the admissible class), then every Nash equilibrium is efficient.

## Proof sketch

Clarke payments make each user's payoff equal to its true utility plus the others' surrogate welfare minus a constant, so best responses are hybrid welfare maximizers; matching each user's surrogate slope to its true marginal utility at the optimum yields an efficient equilibrium.

## Depends on

- [Kelly's proportional allocation mechanism](kellys-proportional-allocation-mechanism.md)
- [Vickrey–Clarke–Groves theorem](../vickrey-clarke-groves-mechanisms/is-incentive-compatible-groves.md)

## Proof depends on

- [VCG with Clarke pivot payments is incentive compatible](../vickrey-clarke-groves-mechanisms/is-incentive-compatible-clarke.md)

## Sources

- Ramesh Johari, "The Price of Anarchy and the Design of Scalable Resource Allocation Mechanisms", Algorithmic Game Theory, Cambridge University Press, 2007.
- Ramesh Johari and John N. Tsitsiklis, "Efficiency of Scalar-Parameterized Mechanisms", Operations Research, 2009.
