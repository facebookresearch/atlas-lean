# Adversarial robust risk and Lipschitz-margin certificates

This node collects the robust-risk definition for multiclass classifiers on a normed input space and
the margin certificate that guarantees a constant prediction on a norm ball.

## Expansion

A sound expansion has separate pages for:

1. **Robust 0-1 risk.** Fix a norm on $\mathbb{R}^d$, a finite label set $Y$ with $\lvert Y \rvert \ge 2$, a radius
   $\varepsilon \ge 0$ and a classifier $h : \mathbb{R}^d \to Y$. For a distribution $D$ on
   $\mathbb{R}^d \times Y$, the robust risk is the probability of the event that some $x'$ with
   $\lVert x' - x \rVert \le \varepsilon$ has $h(x') \ne y$. The page must state a measurability
   convention for this event (for example, measurability of $h$ together with an outer-probability
   definition, or an assumption that makes the event measurable); the Lipschitz argument below does not
   remove this obligation. For $\varepsilon = 0$ the robust risk is the expected 0-1 loss of $h$.
2. **Margin certificate.** Let $f : \mathbb{R}^d \to \mathbb{R}^Y$ be a score map, let $x$ be a point
   and $y \in Y$ a label, and let $L > 0$. Suppose that for every $j \ne y$ the map
   $z \mapsto f_y(z) - f_j(z)$ is $L$-Lipschitz on the ball $\{z : \lVert z - x \rVert \le \varepsilon\}$
   and that $f_y(x) - f_j(x) > L\varepsilon$ for every $j \ne y$ (with $\lvert Y \rvert \ge 2$ this is
   $f_y(x) - \max_{j \ne y} f_j(x) > L\varepsilon$). Then $f_y(z) > f_j(z)$ for every $j \ne y$
   and every $z$ in the ball, so the unique maximizer of $f(z)$ is $y$ throughout the ball. Hein and
   Andriushchenko prove the corresponding guarantee with the local Lipschitz constant given by the
   maximal dual norm of $\nabla f_y - \nabla f_j$ over the ball, for continuously differentiable
   scores; the Lipschitz form above is the same argument with an explicit constant.
3. The relation between the certificate and the robust risk: a certified radius at $x$ with $h=\arg\max f$
   and correct label $y$ removes $(x,y)$ from the robust-error event.

## Depends on

- [The 0-1 loss as an abstract loss](../pac-learning/risk-of-the-0-1-loss/zero-one-loss.md)

## Sources

- M. Hein and M. Andriushchenko, *Formal guarantees on the robustness of a classifier against
  adversarial manipulation*, NeurIPS 2017; arXiv:1705.08475, Theorem 2.1.
  <https://arxiv.org/abs/1705.08475>
