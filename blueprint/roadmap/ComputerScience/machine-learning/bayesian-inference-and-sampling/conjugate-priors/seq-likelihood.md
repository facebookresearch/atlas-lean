# Likelihood of a label sequence

For $\theta \in \mathbb{R}^{n+1}$ and a sequence
$s = (s_0, \dots, s_{N-1})$ of labels in $\{0, \dots, n\}$, the likelihood of $s$ is the
extended nonnegative real $\prod_{m < N} \theta_{s_m}^+$, where $x^+ = \max(x, 0)$.
