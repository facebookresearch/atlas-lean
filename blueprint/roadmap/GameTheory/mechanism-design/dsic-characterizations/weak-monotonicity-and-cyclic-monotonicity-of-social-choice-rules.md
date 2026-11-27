# Weak monotonicity and cyclic monotonicity of social choice rules

A social choice rule $f$ on domains $V_i$ is *weakly monotone* if for every agent $i$, profile $b_{-i}$ and $v, v' \in V_i$ with $a = f(v, b_{-i})$ and $a' = f(v', b_{-i})$, $v'(a') - v'(a) \ge v(a') - v(a)$. It is *cyclically monotone* if for every agent, every $b_{-i}$ and every finite cycle $v^0, v^1, \dots, v^k = v^0$ in $V_i$ with outcomes $a^j = f(v^j, b_{-i})$, $\sum_{j=0}^{k-1} \bigl(v^{j+1}(a^{j+1}) - v^{j+1}(a^{j})\bigr) \ge 0$.

## Depends on

- [Incentive compatibility (quasi-linear, dominant strategies)](../vickrey-clarke-groves-mechanisms/is-incentive-compatible.md)

## Sources

- Noam Nisan, "Introduction to Mechanism Design (for Computer Scientists)", Algorithmic Game Theory, Cambridge University Press, 2007.
