# The exponential loss after $T$ rounds is the product of the normalizers

AdaBoost runs on $m > 0$ training points with labels $y_i \in \{\pm 1\}$ and an arbitrary weak learner; $D_t$ are its weights, $h_t$ the weak hypothesis and $\varepsilon_t$ its weighted error in round $t$, $\alpha_t = \tfrac12 \log((1-\varepsilon_t)/\varepsilon_t)$, and $F_T = \sum_{t<T} \alpha_t h_t$ is the combined score. For every $T$,

$$\frac{1}{m} \sum_i e^{-y_i F_T(x_i)} = \prod_{t < T} Z_t,$$

where $Z_t$ is the normalizer of round $t$. It follows from [unrolling the weights](dist-mul-prod.md) and $\sum_i D_T(i) = 1$, and it identifies the quantity in the [training-error bound by the normalizers](train-err-le-prod.md) as the exponential loss of the combined score.

## Sources

- R. E. Schapire, "Explaining AdaBoost", in B. Schölkopf, Z. Luo and V. Vovk (eds.), *Empirical Inference: Festschrift in Honor of Vladimir N. Vapnik*, Springer (2013), Section 4.
