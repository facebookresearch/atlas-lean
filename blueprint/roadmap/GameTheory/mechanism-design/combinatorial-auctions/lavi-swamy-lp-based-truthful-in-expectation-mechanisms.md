# Lavi–Swamy: LP-based truthful-in-expectation mechanisms

Let agents have nonnegative linear valuations over a fractional feasible polytope $P$ whose integral points are a finite set of outcomes. If an $\alpha$-integrality-gap verifier exists, i.e. for every weight vector $w$ some integral outcome $\omega$ satisfies $w \cdot x / \alpha \le w \cdot \omega$, then for every $x \in P$ the point $x / \alpha$ is a convex combination of integral outcomes (Carr–Vempala decomposition). Compute a VCG-optimal fractional solution $x^*$ with Clarke pivot payments $p_i^F$, scale both by $1/\alpha$, and sample an integral outcome $\omega$ from the decomposition of $x^*/\alpha$; when $\omega$ is drawn, charge agent $i$ the amount $(p_i^F/\alpha) \cdot v_i(\omega) / v_i(x^*/\alpha)$, and $0$ when $v_i(x^*/\alpha) = 0$. This yields a randomized mechanism that is truthful in expectation, individually rational for every outcome of the randomization, never pays an agent, and achieves expected welfare equal to $1/\alpha$ of the fractional optimum. Charging the scaled VCG payment $p_i^F/\alpha$ deterministically instead keeps truthfulness in expectation but can violate individual rationality when an agent draws an outcome it values at $0$.

## Proof sketch

By LP duality the integrality-gap condition says no hyperplane separates $x/\alpha$ from the convex hull of integral outcomes. Expected outcomes equal $x^*/\alpha$ and each agent's expected payment is $p_i^F/\alpha$, so its expected utility is $1/\alpha$ times its VCG utility, which truthfulness maximizes. Individual rationality of VCG gives $p_i^F/\alpha \le v_i(x^*/\alpha)$, so for every drawn $\omega$ the utility $v_i(\omega)\,(1 - (p_i^F/\alpha)/v_i(x^*/\alpha))$ is nonnegative.

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
