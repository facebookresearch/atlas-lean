# Semi-algebraic motion planning instances and input size

An algebraic motion-planning instance describes the obstacle region $C_{\mathrm{obs}}$, induced by semi-algebraic models of the
robot and the obstacles, as a Boolean combination of polynomial inequalities with rational coefficients in the coordinates
of the configuration space $C \subseteq \mathbb{R}^n$, together with an initial and a goal configuration; the question is whether they lie in the same path component of the free space. The size
parameters are the dimension $n$, the number $m$ of polynomials, the maximal degree $d$ and the total bit-length of the
coefficients. Complexity statements are relative to this encoding; for example, an encoding with exponentially more bits than
necessary places the problem in P, which illustrates the encoding's role and is not a theorem about the
problem itself.

## Expansion

This node states a precise definition.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Configuration space, obstacle region and the motion planning problem.

## Sources

- Planning Algorithms, web section 'General algorithms' (Ch. 6 computational complexity) — S. M. LaValle, Planning Algorithms, Sec. 6.5.3: n, m, d parameters for cylindrical algebraic decomposition. <http://www.lavalle.pl/planning/node306.html>
- Planning Algorithms, web section 'Lower bounds for motion planning' (Ch. 6 computational complexity) — S. M. LaValle, Planning Algorithms, Sec. 6.5.1: remark that hardness depends on instance encoding. <https://lavalle.pl/planning/node303.html>
