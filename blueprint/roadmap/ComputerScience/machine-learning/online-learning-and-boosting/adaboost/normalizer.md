# Normalizer of a boosting round

For labels $y$, weights $D$ and predictions $h$ on $m$
training points, let $\varepsilon$ be the weighted training error of $h$ under $D$ and
$\alpha = \alpha(\varepsilon)$ the hypothesis weight. The normalizer of the round is

$$Z = \sum_i D(i) \exp(-\alpha\, y_i h_i),$$

where the label $y_i$ and the prediction $h_i$ are read as $\pm 1$.
