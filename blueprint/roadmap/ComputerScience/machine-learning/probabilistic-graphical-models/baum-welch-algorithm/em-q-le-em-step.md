# The Baum-Welch update maximizes the EM objective

Let $S$ and $O$ be finite sets, let
$T \ge 1$, and let $x_1, \dots, x_N$ with $N \ge 1$ be sequences $x_n = (x_{n,0}, x_{n,1}, \dots)$
of observations in $O$ such that every $o \in O$ equals $x_{n,t}$ for some $n$ and some $t \le T$.
Consider the EM model of a hidden Markov model on states $S$ and observations $O$ whose latent
variable is the state path $z = (z_0, \dots, z_T)$ and whose joint $p_h(x, z)$ is the path weight,
with EM objective $Q(h' \mid h) = \sum_n \sum_z p_h(z \mid x_n) \log p_{h'}(x_n, z)$, where
$p_h(z \mid x) = p_h(x, z) / \sum_{z'} p_h(x, z')$ is the posterior of the path. Then for all valid
hidden Markov models $h$ and $h'$ (positive initial, transition and emission probabilities, each
distribution summing to one), $Q(h' \mid h) \le Q(\bar h \mid h)$, where $\bar h$ is the
Baum-Welch step applied to $h$ on these data.
