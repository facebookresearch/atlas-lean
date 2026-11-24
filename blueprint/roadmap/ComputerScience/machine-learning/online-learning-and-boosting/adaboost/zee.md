# Normalizer of an AdaBoost round

Run AdaBoost on training points with labels $y$, and
read labels and predictions as $\pm 1$. The normalizer of round $t$ is
$Z_t = \sum_i D_t(i) \exp(-\alpha_t y_i h_t(i))$, where $D_t$ are AdaBoost's weights in round
$t$, $h_t$ is the weak hypothesis of round $t$, and $\alpha_t$ is its weight.
