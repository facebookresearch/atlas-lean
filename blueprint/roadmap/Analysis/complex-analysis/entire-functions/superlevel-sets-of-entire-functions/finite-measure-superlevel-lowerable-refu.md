# Gol'dberg's counterexample on superlevel sets of finite measure

This settles [Erdős Problem 1118 on superlevel sets of finite measure](finite-measure-superlevel-lowerable.md) in the negative: its statement is false.

Write $E(c) = \{z \in \mathbb{C} : |f(z)| > c\}$ and $T = \{c > 0 : E(c) \text{ has finite Lebesgue measure}\}$. Gol'dberg proved that for every $m > 0$ there are nonconstant entire functions $f$ with $T = [m, \infty)$. For such an $f$, $E(m)$ has finite measure while $E(c')$ has infinite measure for every $c' < m$ (for $c' \le 0$ because $E(c') \supseteq E(m/2)$), so $f$ is a nonconstant counterexample with $c = m$. Nonconstancy is what matters here: the constant function $f = m$ also has $T = [m, \infty)$, since $E(c)$ is empty for $c \ge m$ and is all of $\mathbb{C}$ for $c < m$, but the linked statement excludes constants. erdosproblems.com/1118 records the negative answer.

## Sources

- T. F. Bloom, Erdős Problems, Problem #1118, https://www.erdosproblems.com/1118 (status SOLVED); resolution: A. A. Gol'dberg, Sets on which the modulus of an entire function has a lower bound, Sibirsk. Mat. Zh. (1979), 512-518, for any m > 0 there are entire f whose set T = \{c > 0 : |E(c)| < ∞\} is [m, ∞) (erdosproblems.com/1118), https://www.erdosproblems.com/1118.
