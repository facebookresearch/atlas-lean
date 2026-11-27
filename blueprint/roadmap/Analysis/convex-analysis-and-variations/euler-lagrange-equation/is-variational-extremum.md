# Variational extremum

Let $a, b$ be real numbers and let $L(t, y, v)$
be a real function of three real variables. A function $x : \mathbb{R} \to \mathbb{R}$ is a
variational extremum of the action of $L$ on $(a, b)$ if $x$ is continuously differentiable and,
for every infinitely differentiable function $h : \mathbb{R} \to \mathbb{R}$ of compact support
whose closed support lies in the open interval $(a, b)$, the derivative at $\varepsilon = 0$ of

$$
\varepsilon \mapsto \int_{(a, b)}
L\big(t, x(t) + \varepsilon h(t), x'(t) + \varepsilon h'(t)\big)\,dt
$$

is $0$.

By convention, a derivative that does not exist is taken to be $0$, and so is the integral of a
function that is not integrable.
