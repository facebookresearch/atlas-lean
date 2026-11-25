# The weights-only step does not decrease the log-likelihood

Let $Z$ be a finite set of latent states and $\iota$ a finite set of items, with fixed item success probabilities $P_z(i) \in (0, 1)$ for each latent state $z$ and item $i$. Let $Z$ be nonempty and $x_1, \dots, x_N$ response patterns with $N \ge 1$. For every valid weight function $w$, the weights-only EM step does not decrease the log-likelihood $\sum_n \log \sum_z w_z P_z(x_n)$ of the data.
