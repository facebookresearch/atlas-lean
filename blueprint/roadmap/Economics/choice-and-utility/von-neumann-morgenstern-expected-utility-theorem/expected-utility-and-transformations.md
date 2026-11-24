# Expected utility is preserved by positive affine but not by all increasing transformations

Let $u : X \to \mathbb{R}$ be an expected-utility representation of a preference over lotteries on a finite set $X$. For $a > 0$ and real $b$, $au + b$ is again an expected-utility representation, since the expected utility of every lottery is transformed by the same increasing affine map. A strictly increasing transformation that is not affine need not be: for $X = \{x, y, z\}$ and $u = (0, 1, 2)$, the lottery $\frac12 x + \frac12 z$ and the sure outcome $y$ have expected utility $1$ each, so they are indifferent, while the strictly increasing $f(t) = t^3$ gives $f \circ u = (0, 1, 8)$ with expected utilities $4$ and $1$, which rank them strictly.

## Depends on

- [Expected-utility representation of a preference](is-expected-utility-representation.md): expected-utility representations.
- [Expected utility of a lottery](expected-utility.md): expected utility of a lottery.

## Background

- [Expected utility is unique up to positive affine transformation](exists-pos-affine.md): the converse: representations are unique up to positive affine transformation.

## Sources

- A. Rubinstein, *Lecture Notes in Microeconomic Theory*, Princeton University Press, Lecture 8 (Expected utility), section "The vNM utilities are unique up to positive affine transformation", <http://assets.press.princeton.edu/rubinstein/lecture8.pdf>
