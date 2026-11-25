# Hyperproperties, hypersafety and k-safety

Let $\Psi_{\mathrm{inf}}$ be the set of infinite traces over a set of states. A *hyperproperty* is a set $\mathbf{H}$ of sets of traces, and a system with trace set $T$ satisfies $\mathbf{H}$ when $T \in \mathbf{H}$. $\mathbf{H}$ is *hypersafety* if for every $T \notin \mathbf{H}$ there is a finite set $M$ of finite traces, each a prefix of a trace of $T$ ("bad thing"), such that no $T'$ having every element of $M$ as a prefix of one of its traces is in $\mathbf{H}$; it is *$k$-safety* if such $M$ can always be chosen with at most $k$ elements; it is *hyperliveness* if every finite set of finite traces can be extended to a member of $\mathbf{H}$.

## Sources

- M. R. Clarkson and F. B. Schneider, "Hyperproperties", *Journal of Computer Security* 18(6):1157–1210, 2010
