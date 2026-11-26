# Stationarity of iterated Bayesian learning

For a prior $\pi$ on a finite hypothesis set and likelihoods $L(\cdot \mid h)$ on a finite data set, one transmission step (draw a datum $d \sim L(\cdot \mid h)$, then a hypothesis from the posterior given $d$) started from $\pi$ returns $\pi$: $\sum_h \pi(h) K(h, h') = \pi(h')$ with $K(h, h') = \sum_d L(d \mid h) P(h' \mid d)$.
