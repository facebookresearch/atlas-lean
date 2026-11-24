# AdaBoost's weights

Given labels $y$ on $m$ training points and a weak learner
$\mathrm{wl}$, which maps weights on the points to a hypothesis's predictions on them,
AdaBoost's weights $D_t$ on the points are defined by $D_0(i) = 1/m$ for every point $i$, and
$D_{t+1}$ is the reweighting of $D_t$ by the hypothesis $\mathrm{wl}(D_t)$.
