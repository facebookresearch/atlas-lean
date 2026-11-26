# EM weights-only step increases the log-likelihood

Let $Z$ be a finite nonempty latent grid and fix item success probabilities $0 < P_z(i) < 1$ on a finite set of items, with locally independent responses given $z$. For data $x_1, \dots, x_N$ with $N \ge 1$ and any positive initial latent weights $w_0$, iterate the weights-only EM step, which replaces the weights by the average posterior over the data. Then the log-likelihood $\ell(w) = \sum_n \log \sum_z w_z P_z(x_n)$ is nondecreasing along the iterates.
