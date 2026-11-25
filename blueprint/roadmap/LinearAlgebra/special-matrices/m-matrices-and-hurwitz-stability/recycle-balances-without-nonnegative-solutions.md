# Recycle balances without nonnegative solutions

Let $K$ be a real square matrix with nonnegative entries and let $f$ have strictly positive entries. If the spectral radius of $K$
is at least $1$, then $x = f + Kx$ has no solution with $x \ge 0$.

Indeed, a solution with $x \ge 0$ has $x \ge f > 0$, and then $Kx = x - f \le (1 - \varepsilon)x$ with
$\varepsilon = \min_i f_i/x_i \in (0, 1]$. In the weighted maximum norm $\lVert y \rVert = \max_i \lvert y_i\rvert/x_i$ the
operator norm of $K$ is at most $1 - \varepsilon$, so the spectral radius of $K$ is below $1$.

For feeds with zero entries the condition is not necessary: $K = \operatorname{diag}(1, 0)$ and $f = (0, 1)$ admit every
$x = (t, 1)$ with $t \ge 0$.

## Depends on

## Proof depends on

## Expansion

Check the statement against a textbook locator for the upper Collatz–Wielandt bound ($Kx \le \beta x$ with $x > 0$ implies a spectral
radius at most $\beta$), and link the page that bounds the spectral radius by an operator norm.

## Sources

- R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd edition, Cambridge University Press, 2013, Section 8.1.
