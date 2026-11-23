# Correlation of one neuron

Let $x_1, \dots, x_n \in \mathbb{R}^d$ have every coordinate in $[-1, 1]$, let
$\sigma \in \{-1, 1\}^n$ be a sign vector and $w \in \mathbb{R}^d$. Let $N \subseteq \mathbb{R}^n$
be the set of value vectors of the [ReLU neurons on the $\ell^1$ unit ball](l1-neuron-values.md).
The neuron with inner weights $w$ is $\lVert w \rVert_1$ times a neuron of the $\ell^1$ unit ball,
so its correlation with $\sigma$ is at most $\lVert w \rVert_1$ times the two one-sided suprema:

$$\Big\lvert \sum_i \sigma_i \max(\langle w, x_i \rangle, 0) \Big\rvert \le \lVert w \rVert_1 \Big( \sup_{v \in N} \sum_i \sigma_i v_i + \sup_{v \in N} \sum_i (-\sigma_i) v_i \Big).$$
