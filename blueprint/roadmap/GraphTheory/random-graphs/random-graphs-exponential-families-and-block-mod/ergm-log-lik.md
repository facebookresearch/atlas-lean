# Log-likelihood of an exponential random graph model

For a finite vertex set $V$, a statistic $t$ of simple graphs on $V$ with values in $\mathbb{R}^\iota$ for a finite index set $\iota$, $\theta \in \mathbb{R}^\iota$ and a graph $y$, the log-likelihood of the exponential random graph model is $\ell(\theta; y) = \langle\theta, t(y)\rangle - \log \kappa(\theta)$ with $\kappa(\theta) = \sum_G e^{\langle\theta, t(G)\rangle}$, the logarithm of the law in Snijders (2002), equation (3).
