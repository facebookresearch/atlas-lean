# Lmsr Loss

For a finite nonempty set of outcomes, a liquidity parameter `b` and an outstanding-share vector `q`, the loss of the logarithmic market scoring rule market maker when outcome `i` occurs after trades from `0` to `q` is `q i - (C(q) - C(0))`, where `C(q) = b · log ∑ⱼ exp(q j / b)` is the LMSR cost function.

At zero liquidity, $b = 0$, every quotient $q_j/b$ is $0$, both costs are $0$ (see the [LMSR cost function](lmsr-cost.md)), and the loss is $q_i$.
