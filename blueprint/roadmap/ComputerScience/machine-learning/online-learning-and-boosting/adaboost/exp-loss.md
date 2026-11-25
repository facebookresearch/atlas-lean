# The exponential loss

For labels $y_i \in \{\pm 1\}$ on $m$ training points and a score vector $F \in \mathbb{R}^m$, the exponential loss is

$$L(F) = \frac{1}{m} \sum_{i=1}^m e^{-y_i F_i}.$$

It upper-bounds the training error of $\operatorname{sign} F$, because $\mathbf{1}[y_i F_i \le 0] \le e^{-y_i F_i}$.

## Sources

- R. E. Schapire, "Explaining AdaBoost", in B. Schölkopf, Z. Luo and V. Vovk (eds.), *Empirical Inference: Festschrift in Honor of Vladimir N. Vapnik*, Springer (2013), Section 4.
