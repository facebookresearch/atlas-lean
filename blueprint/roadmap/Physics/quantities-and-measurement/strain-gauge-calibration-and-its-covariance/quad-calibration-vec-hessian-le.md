# Calibration Hessian norm is at most twice the absolute value of c2

For real coefficients $c_0$, $c_1$ and $c_2$, let $\varphi(y) = c_0 + c_1 y_0 + c_2 y_0^2$ be the
component of the [one-component vector calibration](quad-calibration-vec.md), a function on
one-component real vectors $y = (y_0)$ with the sup norm. At every point $y$ its second Fréchet
derivative has operator norm at most $2\,|c_2|$:

$$
\bigl\|D^2\varphi(y)\bigr\| \le 2\,|c_2|.
$$

As $\varphi$ is a polynomial, its first and second Fréchet derivatives exist everywhere.
