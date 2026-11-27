# Chow–Liu optimality

Let $\iota$ be a finite set of variables, $X = (X_i)_{i \in \iota}$ a random vector with values in
$\prod_i \alpha_i$, each $\alpha_i$ finite, and joint law $P$ (a probability mass function), and let $\tau, \tau'$
be dependence forests, with Chow–Liu approximations $P_\tau, P_{\tau'}$. Then
$D(P \| P_\tau) \le D(P \| P_{\tau'})$ if and only if the mutual-information weight of $\tau'$ is at most that of
$\tau$; so minimizing $D(P \| P_\tau)$ over dependence trees is maximizing the total mutual information
$\sum_i I(X_i; X_{j(i)})$ of their edges.
