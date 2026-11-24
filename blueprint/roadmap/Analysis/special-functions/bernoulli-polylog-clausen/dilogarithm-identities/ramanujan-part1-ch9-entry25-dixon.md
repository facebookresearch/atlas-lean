# Entry 25 of Chapter 9 of Ramanujan's notebooks

Let $x, y \in [0, 1]$ and let $\theta$
and $\varphi$ be real numbers with $x e^{i\theta} + y e^{i\varphi} = xy \, e^{i(\theta + \varphi)}$.
Then $1 - x \cos\theta \ne 0$ and $1 - y \cos\varphi \ne 0$. Put
$A_x = 1 - 2x \cos\theta + x^2$, $A_y = 1 - 2y \cos\varphi + y^2$,
$u_x = \arctan \frac{x \sin\theta}{1 - x \cos\theta}$ and
$u_y = \arctan \frac{y \sin\varphi}{1 - y \cos\varphi}$.
Then $A_x > 0$, $A_y > 0$, the four series
$\sum_{k \ge 1} \frac{x^k \cos k\theta}{k^2}$, $\sum_{k \ge 1} \frac{y^k \cos k\varphi}{k^2}$,
$\sum_{k \ge 1} \frac{x^k \sin k\theta}{k^2}$ and $\sum_{k \ge 1} \frac{y^k \sin k\varphi}{k^2}$
converge absolutely, and

$$
\sum_{k \ge 1} \frac{x^k \cos k\theta}{k^2} + \sum_{k \ge 1} \frac{y^k \cos k\varphi}{k^2} =
\frac{\log A_x \log A_y}{8} - \frac{u_x u_y}{2},
$$



$$
\sum_{k \ge 1} \frac{x^k \sin k\theta}{k^2} + \sum_{k \ge 1} \frac{y^k \sin k\varphi}{k^2} =
-\frac{u_y \log A_x}{4} - \frac{u_x \log A_y}{4}.
$$

## Sources

- Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9.
