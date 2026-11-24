# Neyman's variance estimator

For a finite population with potential outcomes $y_{0i}, y_{1i}$ and a treated set $S$, Neyman's variance estimator is

$$\hat V(S) = \frac{s_{1,S}^2}{|S|} + \frac{s_{0,S^c}^2}{|S^c|},$$

with the [sample variances](sample-var.md) of the treated outcomes over $S$ and of the control outcomes over $S^c$ (a division by $0$ read as $0$).
