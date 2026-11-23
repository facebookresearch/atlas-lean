# Unrolling the weights

Run AdaBoost with labels $y$ on $m > 0$ training points and a
weak learner, and let $D_T$ be the weights on the points after $T$ rounds, $Z_t$ the normalizer
of round $t$, and $F_T$ the combined score after $T$ rounds. Then for every $T \in \mathbb{N}$ and
every training point $i$,

$$D_T(i) \cdot m \prod_{t < T} Z_t = \exp(-y_i F_T(i)),$$

where the label $y_i$ is read as $\pm 1$.
