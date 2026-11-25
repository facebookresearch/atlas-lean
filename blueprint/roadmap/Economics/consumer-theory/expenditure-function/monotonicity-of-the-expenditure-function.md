# Monotonicity of the expenditure function

Let $u : \mathbb{R}^L_{\ge 0} \to \mathbb{R}$ be continuous, let $p \in \mathbb{R}^L$ with every $p_\ell > 0$, and let $\bar u$ be an attained utility level, $\bar u \in u(\mathbb{R}^L_{\ge 0})$. Then $e(p, \bar u) = \min\{p \cdot x : x \ge 0,\ u(x) \ge \bar u\}$ is attained, and it is nondecreasing in each price. As a function of $\bar u$ on the attained levels it is nondecreasing, and strictly increasing on attained levels $\bar u \ge u(0)$: if $u(0) \le \bar u_1 < \bar u_2$ and $x_2$ attains $e(p, \bar u_2)$, then $x_2 \ne 0$ and, by continuity, $u(tx_2) \ge \bar u_1$ for some $t < 1$, so $e(p, \bar u_1) \le t\,p \cdot x_2 < e(p, \bar u_2)$. For $\bar u \le u(0)$, $e(p, \bar u) = 0$.

## Background

- [Expenditure is homogeneous of degree one in prices](expenditure-smul.md): homogeneity of degree one in prices.
- [Expenditure is concave on strictly positive prices](concave-on-expenditure-pos.md): concavity in prices.

## Sources

- S. Athey, *Consumer Theory*, lecture notes, MIT 14.121, Fall 1998, §V, Proposition 2(ii), <http://web.mit.edu/athey/www/14.121.fall98/consumer_theory_f98.pdf>
