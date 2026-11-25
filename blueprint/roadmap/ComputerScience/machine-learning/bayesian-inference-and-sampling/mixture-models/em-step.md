# One EM step for the Bernoulli mixture

Let $x_1, \dots, x_N \in \{0, 1\}^d$ be data with
$N \ge 1$ in which every coordinate takes both values. For valid parameters $\theta$ of a mixture
of $K$ products of $d$ Bernoulli distributions, the EM step maps $\theta$ to the parameters with
mixing weights $\pi'_k = N_k / N$ and success probabilities $p'_{kj} = A_{kj} / N_k$, where
$r_{nk}$ is the posterior probability of component $k$ given $x_n$ under $\theta$,
$N_k = \sum_n r_{nk}$, and $A_{kj}$ is the sum of $r_{nk}$ over the points with $x_{nj} = 1$. On
such data these parameters are again valid.
