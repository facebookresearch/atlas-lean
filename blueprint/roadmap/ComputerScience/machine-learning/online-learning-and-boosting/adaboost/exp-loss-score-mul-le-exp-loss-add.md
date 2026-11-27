# No step along any hypothesis beats the factor $2\sqrt{\varepsilon(1-\varepsilon)}$

AdaBoost runs on $m > 0$ training points with labels $y_i \in \{\pm 1\}$ and an arbitrary weak learner; $D_t$ are its weights, $h_t$ the weak hypothesis and $\varepsilon_t$ its weighted error in round $t$, $\alpha_t = \tfrac12 \log((1-\varepsilon_t)/\varepsilon_t)$, and $F_T = \sum_{t<T} \alpha_t h_t$ is the combined score. For every hypothesis $h$, with $\varepsilon$ its weighted error under $D_T$, and every step $a \in \mathbb{R}$,

$$L(F_T) \cdot 2 \sqrt{\varepsilon (1 - \varepsilon)} \le L(F_T + a h),$$

where $L$ is the [exponential loss](exp-loss.md). The proof is the arithmetic-geometric mean inequality applied to $(1-\varepsilon)e^{-a} + \varepsilon e^{a}$.

## Sources

- R. E. Schapire, "Explaining AdaBoost", in B. Schölkopf, Z. Luo and V. Vovk (eds.), *Empirical Inference: Festschrift in Honor of Vladimir N. Vapnik*, Springer (2013), Section 4.
