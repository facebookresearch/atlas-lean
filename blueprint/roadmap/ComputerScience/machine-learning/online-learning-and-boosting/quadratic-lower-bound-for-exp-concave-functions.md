# Quadratic lower bound for exp-concave functions

Let $K \subseteq \mathbb{R}^n$ be convex with diameter $D$, and let $f : K \to \mathbb{R}$ be convex and $\alpha$-exp-concave ($x \mapsto e^{-\alpha f(x)}$ is concave on $K$, $\alpha > 0$) with (sub)gradients
bounded in norm by $G$. For every
$\gamma \le \tfrac12 \min\{1/(GD), \alpha\}$ and all $x, y \in K$,

$$f(x) \ge f(y) + \nabla f(y)^{\mathsf T}(x - y) + \tfrac{\gamma}{2} (x - y)^{\mathsf T} \nabla f(y) \nabla f(y)^{\mathsf T} (x - y).$$

## Related topics

- [Online Newton Step for exp-concave losses](online-newton-step-for-exp-concave-losses.md)

## Sources

- E. Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207, Lemma 4.3. <https://arxiv.org/pdf/1909.05207>
