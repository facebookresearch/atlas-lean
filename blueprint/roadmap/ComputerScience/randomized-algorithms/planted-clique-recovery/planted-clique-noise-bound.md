# Operator-norm bound for the planted noise

For the planted graph $G(n, 1/2, S)$, with probability at least $1 - 2e^{-n}$ the signed adjacency matrix $M$ satisfies $\|M - \mathbf{1}_S\mathbf{1}_S^\top\|_{\mathrm{op}} \le 36\sqrt{n} + 1$, and with probability at least $1 - n e^{-|S|/32}$ every vertex outside $S$ has at most $5|S|/8$ neighbours in $S$. In particular, if $|S| \ge 1024\sqrt{n}$ the perturbation is at most $|S|/16$.

## Proof sketch

The noise is a symmetric matrix of independent centered $\pm 1$ entries, whose operator norm is $O(\sqrt{n})$ with exponentially small failure by an $\varepsilon$-net argument; outside degrees into $S$ are binomial with mean $|S|/2$, so Hoeffding plus a union bound controls them.

## Depends on

- [The planted clique model and recovery](planted-clique-model.md)
- [Two-sided Hoeffding inequality for Bernoulli sums](../../../Probability/concentration-inequalities/hoeffding-s-inequality/hoeffding-bernoulli-sum-abs-tail.md)

## Sources

- N. Alon, M. Krivelevich and B. Sudakov, "Finding a Large Hidden Clique in a Random Graph", Random Structures & Algorithms 13(3-4), 1998.
