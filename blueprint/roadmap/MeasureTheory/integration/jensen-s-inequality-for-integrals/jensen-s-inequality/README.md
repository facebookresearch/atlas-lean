# Jensen's inequality

Let $\varphi \colon \mathbb{R} \to \mathbb{R}$ be convex and let $X$ be a random variable on a probability
space with $E|X| < \infty$ and $E|\varphi(X)| < \infty$. Then $\varphi(EX) \le E\varphi(X)$.

## Idea

A convex function lies above each of its supporting lines: at $c = EX$ there is a slope $a$ with
$\varphi(x) \ge \varphi(c) + a(x - c)$ for all $x$, and taking expectations gives the inequality. Special cases are
$|EX| \le E|X|$, $(EX)^2 \le E(X^2)$ and $e^{EX} \le E e^X$; applied to $\varphi = \exp$ and $\log Y$, for a positive
random variable $Y$ with finitely many values, it gives the inequality between weighted geometric and arithmetic means.
The same argument gives $\varphi\big(\int g \, d\nu\big) \le \int \varphi \circ g \, d\nu$ for every probability measure
$\nu$ and integrable $g$ with $\varphi \circ g$ integrable, with the inequality reversed for concave $\varphi$.

## Statements

- [Jensen's inequality](jensen-inequality.md)
- [Finite Jensen inequality for concave functions](finite-jensen-inequality-for-concave-functions.md): the finite form for a concave function on a convex set, as used for the logarithm

## Background

- [Lebesgue integral](../../nonnegative-lebesgue-integral/lebesgue-integral/README.md): expectations are integrals
- [Measurable functions](../../../measurable-spaces/measurable-spaces-and-measurable-functions/measurable-functions/README.md): random variables

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Theorem 1.6.2 (version read: the author's January 2019 PDF).
