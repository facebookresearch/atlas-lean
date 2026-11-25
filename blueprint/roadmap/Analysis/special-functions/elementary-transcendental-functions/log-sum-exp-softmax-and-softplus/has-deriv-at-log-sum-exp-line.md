# Directional derivative of log-sum-exp

With $\operatorname{lse}(z) = \log \sum_i e^{z_i}$ and $\operatorname{softmax}(z)_i = e^{z_i} / \sum_j e^{z_j}$ on a nonempty finite index set, for all $z, v$ the function $t \mapsto \operatorname{lse}(z + t v)$ is differentiable at $0$ with derivative $v \cdot \operatorname{softmax}(z)$.
