# Warmup and inverse-square-root learning-rate decay

For model dimension $d>0$, positive integer warmup length $w$ and update index $t\ge1$, the original Transformer uses Adam with rate

$$\eta_t=d^{-1/2}\min(t^{-1/2},\,t\,w^{-3/2}).$$

The second branch is the smaller one for $t\le w$: the rate rises linearly to $1/\sqrt{dw}$, then falls as $t^{-1/2}$. This scalar schedule is shared by all coordinates; it is separate from Adam’s coordinatewise normalization.

## Depends on

- [Adam with bias-corrected moments](adam-optimizer.md)

## Background

- [Gradient descent with a step schedule](../../../Analysis/convex-analysis-and-variations/gradient-descent/gradient-descent-trajectory.md)

## Sources

- Vaswani et al., [*Attention Is All You Need*](https://arxiv.org/abs/1706.03762) (NeurIPS 2017), §5.3, equation (3).
