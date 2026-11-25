# The exponential loss along a coordinate

AdaBoost runs on $m > 0$ training points with labels $y_i \in \{\pm 1\}$ and an arbitrary weak learner; $D_t$ are its weights, $h_t$ the weak hypothesis and $\varepsilon_t$ its weighted error in round $t$, $\alpha_t = \tfrac12 \log((1-\varepsilon_t)/\varepsilon_t)$, and $F_T = \sum_{t<T} \alpha_t h_t$ is the combined score. For every hypothesis $h$ and step $a \in \mathbb{R}$,

$$L(F_T + a h) = L(F_T) \sum_i D_T(i)\, e^{-a y_i h(x_i)},$$

where $L$ is the [exponential loss](exp-loss.md): AdaBoost's weights $D_T$ are the normalized per-example exponential losses of $F_T$, so moving along a coordinate rescales the loss by a $D_T$-average.
