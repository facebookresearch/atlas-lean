# AdamW: decoupled weight decay

Use Adam’s bias-corrected moments of the **unregularized** gradient. With base learning rate $\alpha>0$, decay coefficient $\lambda\ge0$ and schedule multiplier $s_t\ge0$, the AdamW convention of Loshchilov and Hutter is

$$\theta_t=(1-s_t\lambda)\theta_{t-1}-s_t\alpha\frac{\widehat m_t}{\sqrt{\widehat v_t}+\epsilon}.$$

The decay term bypasses the moment estimates. In contrast, differentiating an added $\lambda\|\theta\|^2/2$ penalty adds $\lambda\theta$ to the gradient *before* both moments are computed. With coordinatewise adaptive scaling these are different operations. In parameterizations that write $1-\eta_t w$, one sets $\eta_t=s_t\alpha$ and $w=\lambda/\alpha$.

## Depends on

- [Adam with bias-corrected moments](adam-optimizer.md)

## Sources

- Loshchilov and Hutter, [*Decoupled Weight Decay Regularization*](https://arxiv.org/abs/1711.05101) (ICLR 2019), §2, algorithm 2.
