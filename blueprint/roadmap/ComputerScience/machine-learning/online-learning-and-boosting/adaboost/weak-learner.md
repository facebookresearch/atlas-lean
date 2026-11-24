# The weak-learning assumption

A weak learner, which maps weights on the $m$ training
points with labels $y$ to a hypothesis on those points, has edge $\gamma$ if for every weighting
$D$ of the training points with $D_i > 0$ for all $i$ and $\sum_i D_i = 1$, the hypothesis it
returns on $D$ has weighted error under $D$ in the interval $(0, 1/2 - \gamma]$.
