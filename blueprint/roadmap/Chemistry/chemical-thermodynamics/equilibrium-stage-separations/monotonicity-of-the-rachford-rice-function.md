# Monotonicity of the Rachford–Rice function

In the setting of the flash balance, let $g(\beta) = \sum_i z_i (K_i - 1)/(1 + \beta(K_i - 1))$ on $[0, 1]$. If $K_i \ne 1$ for
some $i$ with $z_i > 0$, then $g$ is strictly decreasing, since $g'(\beta) = -\sum_i z_i (K_i - 1)^2/(1 + \beta(K_i - 1))^2 < 0$.
Then $g$ has a root in $(0, 1)$ if and only if $g(0) = \sum_i z_i K_i - 1 > 0$ and $g(1) = 1 - \sum_i z_i/K_i < 0$, that is,
$\sum_i z_i K_i > 1$ and $\sum_i z_i/K_i > 1$; the root is then unique. The root is $\beta = 0$ when $\sum_i z_i K_i = 1$ and
$\beta = 1$ when $\sum_i z_i/K_i = 1$. If $K_i = 1$ for every $i$ with $z_i > 0$, then $g \equiv 0$ and every $\beta$ is a root.

## Depends on

- [Flash balance and the Rachford–Rice equation](flash-balance-and-the-rachford-rice-equation.md)

## Proof depends on

## Sources

- M. Adewumi, *Phase Relations in Reservoir Engineering*, LibreTexts, Section 13.2, the Rachford–Rice objective function, <https://eng.libretexts.org/Bookshelves/Chemical_Engineering/Phase_Relations_in_Reservoir_Engineering_(Adewumi)/13%3A_Elementary_Vapor-Liquid_Equilibrium_II/13.02%3A_Objective_Function_and_Newton-Raphson_Procedure>.
