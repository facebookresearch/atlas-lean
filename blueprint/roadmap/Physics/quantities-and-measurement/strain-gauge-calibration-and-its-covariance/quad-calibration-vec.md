# Quadratic calibration as a map on one-component vectors

For real coefficients $c_0$, $c_1$ and $c_2$, the [quadratic calibration](quad-calibration.md)
$f(v) = c_0 + c_1 v + c_2 v^2$ is also read as the map $F$ from one-component real vectors
$y = (y_0)$ to one-component real vectors,

$$
F(y) = \bigl(f(y_0)\bigr),
$$

which is the form used by the componentwise first-order remainder bounds for maps between real
coordinate spaces with the sup norm. When $x$ and $x + \delta$ lie in a voltage interval $[a, b]$,
the first-order remainder of $F$ at $x$ is at most
$2 |c_2| / 2 \cdot \|\delta\|^2 = |c_2|\, \|\delta\|^2$ in absolute value
([remainder bound on an interval](quad-calibration-vec-remainder-le.md)), an instance of the
[remainder bound from a Hessian bound](../covariance-propagation-and-lipschitz-error-bound/jacobian-remainder-component-le-of-hessi.md).
