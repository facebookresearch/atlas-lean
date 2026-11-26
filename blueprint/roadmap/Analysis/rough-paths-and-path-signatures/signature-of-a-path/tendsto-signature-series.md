# Linear controlled equations are solved by the signature series

Let $\iota$ be finite, $E$ a real Banach space, $A_i : E \to E$ continuous linear maps, and let
the velocity $v$ of $X$ be continuous and bounded, $|v^i(t)| \le M$. If $y : \mathbb{R} \to E$
satisfies $y(s) = y_0$ and

$$y'(t) = \sum_i v^i(t)\, A_i\, y(t) \qquad (t \in \mathbb{R}),$$

then for every $t$ the truncated signature series $\sum_{|w| \le n} S(X)^w_{s,t}\, A_w y_0$
converge to $y(t)$ as $n \to \infty$:

$$y_t = \sum_{w} S(X)^w_{s,t}\, A_{w}\, y_s, \qquad A_{i_1 \cdots i_k} = A_{i_k} \circ \cdots \circ A_{i_1}.$$

The response of every linear system to the path is thus a fixed linear function of the
signature, which is why the signature is the natural feature set of a stream. Boundedness of $v$
is used only to have a global Lipschitz constant for the Picard theorem; for
$X_t = t$ and $A = \mathrm{id}$ the series is $\sum_k (t-s)^k/k!\; y_0 = e^{t-s} y_0$.

## Background

- [Picard iteration](../../ordinary-differential-equations/picard-iteration/README.md):
  the convergence theorem for Picard iterates applied here.
- [Linear systems and fundamental matrices](../../ordinary-differential-equations/linear-systems-and-fundamental-matrices/README.md):
  for a single letter with $X_t = t$ this is the exponential series of a linear system.

## Sources

- T. Lyons, *Rough paths, signatures and the modelling of functions on streams*, Proc. ICM 2014,
  arXiv:1405.4537, §4.2, equation (1).
- I. Chevyrev and A. Kormilitzin, *A primer on the signature method in machine learning*,
  arXiv:1603.03788v2, §1.2.3 and Exercise 1.10 (the factorial bound that makes the series
  converge).
