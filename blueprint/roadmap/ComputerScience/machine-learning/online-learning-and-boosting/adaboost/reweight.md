# AdaBoost reweighting

For labels $y$, weights $D$ and predictions $h$ on $m$ training
points, let $\varepsilon$ be the weighted training error of $h$ under $D$,
$\alpha = \alpha(\varepsilon)$ the hypothesis weight and $Z$ the normalizer of the round. The
reweighted weight of point $i$ is

$$D'(i) = \frac{D(i) \exp(-\alpha\, y_i h_i)}{Z},$$

where the label $y_i$ and the prediction $h_i$ are read as $\pm 1$.
