# Conjugate partition

Let $\lambda = [\lambda_1, \dots, \lambda_L]$ be a finite list of
natural numbers, with $L \ge 0$. Its conjugate $\lambda'$ is the empty list if $L = 0$, and
otherwise the list $[\lambda'_1, \dots, \lambda'_{\lambda_1}]$ of length $\lambda_1$ with
$\lambda'_j = \#\{i : 1 \le i \le L,\ \lambda_i \ge j\}$ for $1 \le j \le \lambda_1$. The length
is set by the first entry $\lambda_1$, and the entries of $\lambda'$ are weakly decreasing and at
least $1$.

When $\lambda$ is a partition, $\lambda_1 \ge \dots \ge \lambda_L \ge 1$, its first entry is its
largest part, and $\lambda'$ is the conjugate partition: its Young diagram is the transpose of the
Young diagram of $\lambda$.
