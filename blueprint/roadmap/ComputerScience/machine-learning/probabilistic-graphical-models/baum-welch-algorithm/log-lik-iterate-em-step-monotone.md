# The log-likelihood is monotone along the Baum-Welch iterates

Let $S$ and $O$ be finite
sets, let $T \ge 1$, and let $x_1, \dots, x_N$ with $N \ge 1$ be sequences
$x_n = (x_{n,0}, x_{n,1}, \dots)$ of observations in $O$ such that every $o \in O$ equals $x_{n,t}$
for some $n$ and some $t \le T$. Let $h_0$ be a valid hidden Markov model on states $S$ and
observations $O$ and let $h_t$ be the result of $t$ Baum-Welch steps from $h_0$ on these data.
Then $t \mapsto \ell(h_t)$ is monotone (nondecreasing in $t \in \mathbb{N}$), where
$\ell(h) = \sum_{n=1}^{N} \log \sum_z p_h(x_n, z)$ is the log-likelihood of the EM model of $h$,
the sum ranging over state paths $z = (z_0, \dots, z_T)$ and $p_h(x, z)$ being the path weight.
