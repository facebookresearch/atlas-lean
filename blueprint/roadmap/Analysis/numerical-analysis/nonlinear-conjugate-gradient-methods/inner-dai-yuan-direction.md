# The Dai–Yuan identity

Let $g, g', d$ be vectors of a real inner product space with $d^\top (g' - g) \ne 0$, and let
$d' = -g' + \beta d$ with the [Dai–Yuan parameter](dai-yuan-beta.md)
$\beta = \|g'\|^2 / d^\top (g' - g)$. Then

$$g'^\top d' = \beta\, g^\top d .$$

Equivalently $\beta = g'^\top d' / g^\top d$. The identity propagates the sign of the directional
derivative from one search direction to the next, and the source calls it "very important in our
convergence analysis".

Proof: $g'^\top d' = -\|g'\|^2 + \beta\, g'^\top d$ and
$\beta\, g^\top d = \beta\, g'^\top d - \beta\, d^\top (g' - g) = \beta\, g'^\top d - \|g'\|^2$.

## Sources

- Y. H. Dai and Y. Yuan, *A nonlinear conjugate gradient method with a strong global convergence property*, SIAM J. Optim. 10 (1999), 177–182, equations (2.5) and (2.6).
