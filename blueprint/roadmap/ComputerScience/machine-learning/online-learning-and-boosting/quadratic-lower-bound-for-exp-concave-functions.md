# Quadratic lower bound for exp-concave functions

Let $F$ be a real Hilbert space (for instance $\mathbb{R}^n$), let $K \subseteq F$ be convex and bounded with diameter at most $D$, and let $\alpha > 0$. Let $f : K \to \mathbb{R}$ be $\alpha$-exp-concave: $x \mapsto e^{-\alpha f(x)}$ is concave on $K$. Let $y \in K$, and let $g$ be a gradient of $f$ at $y$ relative to $K$, that is $f(x') = f(y) + \langle g, x' - y \rangle + o(\lVert x' - y \rVert)$ as $x' \to y$ in $K$ (for instance $g = \nabla f(y)$ when $f$ is differentiable at $y$), with $\lVert g \rVert \le G$. Then for every real $\gamma$ with $2\gamma \le \alpha$ and $2\gamma G D \le 1$, that is
$\gamma \le \tfrac12 \min\{1/(GD), \alpha\}$ with $1/(GD) = +\infty$ when $GD = 0$, and for every $x \in K$,

$$f(x) \ge f(y) + \langle g, x - y \rangle + \tfrac{\gamma}{2} \langle g, x - y \rangle^2.$$

In $\mathbb{R}^n$ with $g = \nabla f(y)$ this reads $f(x) \ge f(y) + \nabla f(y)^{\mathsf T}(x - y) + \tfrac{\gamma}{2} (x - y)^{\mathsf T} \nabla f(y) \nabla f(y)^{\mathsf T} (x - y)$.

Convexity of $f$, which Hazan's definition of exp-concavity includes, is not assumed; the bound $G$ is needed only at $y$; and $\gamma$ may be zero or negative. The cases $G = 0$ and $D = 0$ are allowed: then every $\gamma \le \alpha/2$ qualifies.

## Proof

Since $0 < 2\gamma \le \alpha$, the function $h = e^{-2\gamma f} = (e^{-\alpha f})^{2\gamma/\alpha}$ is concave on $K$, as $t \mapsto t^{2\gamma/\alpha}$ is concave and nondecreasing on $[0, \infty)$. Its first-order condition at $y$ gives $e^{-2\gamma f(x)} \le e^{-2\gamma f(y)} (1 - u)$ with $u = 2\gamma \langle g, x - y \rangle$. As $\lvert u \rvert \le 2\gamma G D \le 1$ and $1 - u \le e^{-(u + u^2/4)}$ for $u \ge -1$, this gives $2\gamma (f(x) - f(y)) \ge u + u^2/4$, the claim. For $\gamma \le 0$ the quadratic term is nonpositive, and the claim follows from the case of a small positive $\gamma$.

## Related topics

- [Online Newton Step for exp-concave losses](online-newton-step-for-exp-concave-losses.md)

## Sources

- E. Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207 (v3), Section 4.2: Definition 4.1 and Lemma 4.3, pp. 59–60. <https://arxiv.org/pdf/1909.05207>
