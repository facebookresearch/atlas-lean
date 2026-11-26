# Inverse of a Riordan array from its A- and Z-sequences (one-sided form)

Let $K$ be a
field, let $g, f, A, Z, \bar f$ be formal power series over $K$, and let $d_{00} \in K$ with
$d_{00} \ne 0$. Suppose that $g(0) = d_{00}$, $f(0) = 0$, $A(0) \ne 0$, $\bar f(0) = 0$,
$f(\bar f(x)) = x$, $f(x) = x\, A(f(x))$ and $g(x) = d_{00} \bigl(1 - x\, Z(f(x))\bigr)^{-1}$.
Then

$$\left(\frac{1}{g(\bar f(x))},\ \bar f(x)\right) =
\left(\frac{A(x) - x\, Z(x)}{d_{00}\, A(x)},\ \frac{x}{A(x)}\right).$$

Here $A$ and $Z$ are the generating functions of the A- and Z-sequences of the Riordan array
$(g, f)$, and the pair on the left is its inverse. Only $f(\bar f(x)) = x$ is assumed, not also
$\bar f(f(x)) = x$.
