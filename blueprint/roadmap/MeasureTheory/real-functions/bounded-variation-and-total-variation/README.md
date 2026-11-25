# Functions of bounded variation

Let $\alpha$ be a linearly ordered set, such as $\mathbb{R}$, let $s \subseteq \alpha$, and let $f$ be a function on
$\alpha$ with values in a space with an extended pseudodistance $d$, such as a metric space like $\mathbb{C}$. The
variation of $f$ on $s$ is the supremum of $\sum_{i < n} d(f(u_{i+1}), f(u_i))$ over all finite nondecreasing sequences
$u_0 \le u_1 \le \cdots \le u_n$ of points of $s$, a number in $[0, \infty]$, and $f$ has bounded variation on $s$ if
its variation is finite. This is the general form of a function of bounded variation on $\mathbb{R}$: for
$F \colon \mathbb{R} \to \mathbb{C}$ and $s = \mathbb{R}$ the variation is $\sup_x T_F(x)$, where $T_F(x)$ is the
variation of $F$ on $(-\infty, x]$, so $F$ has bounded variation on $\mathbb{R}$ exactly when its total variation
function $T_F$ is bounded.

## Idea

A monotone real function on $[a, b]$ has variation $|f(b) - f(a)|$. By Jordan's decomposition, a real function of
bounded variation on an interval of $\mathbb{R}$ is the difference of two increasing functions there, so it is
differentiable almost everywhere on the interval and has at most countably many discontinuities. Absolutely continuous
functions have bounded variation on bounded intervals, while $x \sin(1/x)$, extended by $0$ at $0$, is continuous on
$[0, 1]$ without bounded variation. A complex Borel measure $\nu$ on $\mathbb{R}$ has the distribution function
$x \mapsto \nu((-\infty, x])$, which is right-continuous, of bounded variation and tends to $0$ at $-\infty$, and every
such function comes from exactly one such measure.

## Statements

- [Function of bounded variation on a set](bounded-variation-on.md)
