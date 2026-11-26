# Each Baum-Welch step does not decrease the log-likelihood

Let $S$ and $O$ be finite
sets, let $T \ge 1$, and let $x_1, \dots, x_N$ with $N \ge 1$ be sequences
$x_n = (x_{n,0}, x_{n,1}, \dots)$ of observations in $O$ such that every $o \in O$ equals $x_{n,t}$
for some $n$ and some $t \le T$. For every valid hidden Markov model $h$ on states $S$ and
observations $O$, $\ell(h) \le \ell(\bar h)$, where $\bar h$ is the Baum-Welch step applied to $h$
on these data and $\ell(h) = \sum_{n=1}^{N} \log \sum_z p_h(x_n, z)$ is the log-likelihood of the
EM model of $h$, the sum ranging over state paths $z = (z_0, \dots, z_T)$ and $p_h(x, z)$ being the
path weight.
