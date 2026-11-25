# The weighted centroid decomposition

Let $F$ be a real inner product space, $s$ a finite
index set, $w_i \in \mathbb{R}$ weights with $W = \sum_{i \in s} w_i \ne 0$, and $x_i \in F$
points for $i \in s$, and let $m = W^{-1} \sum_{i \in s} w_i x_i$. Then for every $c \in F$,

$$\sum_{i \in s} w_i \|x_i - c\|^2 = \sum_{i \in s} w_i \|x_i - m\|^2 + W \|m - c\|^2.$$

This is the weighted version of the centroid decomposition behind $k$-means. When $W > 0$ it
shows that $m$ minimizes $c \mapsto \sum_{i \in s} w_i \|x_i - c\|^2$.
