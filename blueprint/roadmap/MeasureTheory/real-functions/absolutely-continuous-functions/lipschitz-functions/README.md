# Lipschitz functions are the absolutely continuous functions with bounded derivative

Let $f : \mathbb{R} \to \mathbb{R}$ and $M \ge 0$. Then $|f(x) - f(y)| \le M |x - y|$ for all $x$ and
$y$ if and only if $f$ is absolutely continuous on every closed bounded interval and
$|f'(x)| \le M$ for almost every $x$, where $f'(x)$ is taken to be $0$ at points where $f$ is not
differentiable.

## Idea

Absolutely continuous functions are exactly those that are integrals of their derivatives,
$f(y) - f(x) = \int_x^y f'$, by the fundamental theorem of calculus for the Lebesgue integral. So a
bound $|f'| \le M$ almost everywhere gives the Lipschitz bound; conversely, a Lipschitz function is
absolutely continuous, with $\delta = \varepsilon / (1 + M)$, and its difference quotients are bounded
by $M$. The Cantor function shows why absolute continuity is needed: it is continuous with
derivative $0$ almost everywhere, yet not constant.

## Statements

- [Lipschitz functions are the absolutely continuous functions with bounded derivative](lipschitz-with-iff-absolutely-continuous.md)
- [A $1$-Lipschitz function on $[a,b]$ is absolutely continuous with essentially bounded derivative](absolutely-continuous-on-interval-and-e.md): a local form of one direction, for $M = 1$: a function $1$-Lipschitz on $[a, b]$ is absolutely continuous there, with essentially bounded derivative.

## Background

- [Absolute continuity on an interval](../absolute-continuity-on-an-interval/README.md): the definition
