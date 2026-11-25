# Weighted training error

For labels $y$, weights $D$ and predictions $h$ on $m$ training
points, the weighted training error of $h$ under $D$ is $\sum_{i : h(i) \ne y(i)} D(i)$, the total
weight of the points that $h$ misclassifies.
