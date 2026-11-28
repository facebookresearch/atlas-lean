# The derivative of the softmax regression risk

For a finite nonempty set of classes $C$ with decidable equality and data $(X_k, Y_k)_{k < m}$ with $X_k \in \mathbb{R}^\iota$ and $Y_k \in C$, the empirical softmax-regression risk $W \mapsto \sum_k -\log \operatorname{softmax}(W X_k)_{Y_k}$ is differentiable at every weight matrix $W$, with derivative $V \mapsto \sum_k \sum_c (\operatorname{softmax}(W X_k)_c - [Y_k = c])\, (V_c \cdot X_k)$.
