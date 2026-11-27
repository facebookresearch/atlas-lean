# Lavi–Swamy: LP-based truthful-in-expectation mechanisms

Let agents have linear valuations over a fractional feasible polytope $P$ whose integral points are a finite set of outcomes. If an $\alpha$-integrality-gap verifier exists, i.e. for every weight vector $w$ some integral outcome $\omega$ satisfies $w \cdot x / \alpha \le w \cdot \omega$, then for every $x \in P$ the point $x / \alpha$ is a convex combination of integral outcomes (Carr–Vempala decomposition). Computing a VCG-optimal fractional solution, scaling by $1/\alpha$, sampling an integral outcome from the decomposition and scaling the VCG payments by $1/\alpha$ yields a randomized mechanism that is truthful in expectation, ex-post individually rational with no positive transfers, and achieves expected welfare equal to $1/\alpha$ of the fractional optimum.

## Proof sketch

By LP duality the integrality-gap condition says no hyperplane separates $x/\alpha$ from the convex hull of integral outcomes. Expected outcomes equal $x/\alpha$ and expected payments are scaled VCG payments, so each agent's expected utility is $1/\alpha$ times its VCG utility, which truthfulness maximizes.

## Depends on

- [Universally truthful and truthful-in-expectation randomized mechanisms](../dsic-characterizations/universally-truthful-and-truthful-in-expectation-randomized-mechanisms.md)
- [Vickrey–Clarke–Groves theorem](../vickrey-clarke-groves-mechanisms/is-incentive-compatible-groves.md)
- [Integrality gaps of linear programming relaxations](../../../ComputerScience/approximation-algorithms/lp-based-approximation/integrality-gaps-of-linear-programming.md)

## Proof depends on

- [VCG with Clarke pivot payments is incentive compatible](../vickrey-clarke-groves-mechanisms/is-incentive-compatible-clarke.md)

## Sources

- Ron Lavi and Chaitanya Swamy, "Truthful and Near-Optimal Mechanism Design via Linear Programming", Journal of the ACM, 2011.
- Robert D. Carr and Santosh Vempala, "Randomized Metarounding", Random Structures & Algorithms, 2002.
- Ron Lavi, "Computationally Efficient Approximation Mechanisms", Algorithmic Game Theory, Cambridge University Press, 2007.
