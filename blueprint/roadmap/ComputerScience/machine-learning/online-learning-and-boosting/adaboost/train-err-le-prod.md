# The training error is at most the product of the normalizers

Let AdaBoost run on
$m > 0$ training points with labels $y$ and an arbitrary weak learner, and write $Z_t$ for the
normalizer of round $t$. Then for every number of rounds $T$, the training error after $T$ rounds
is at most $\prod_{t < T} Z_t$.
