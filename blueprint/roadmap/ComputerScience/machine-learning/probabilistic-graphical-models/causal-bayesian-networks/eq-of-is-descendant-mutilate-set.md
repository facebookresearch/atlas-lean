# Intervened nodes descend only from themselves

Let $B$ be a Bayesian network on the nodes $0, \dots, n - 1$ with values in $\alpha$, $W$ a finite
set of nodes and $w \in \alpha^n$. In the [mutilated network](mutilate-set.md) of
$\mathrm{do}(X_W = w)$, where the arrows into $W$ are removed, a node $j \in W$ is a descendant
only of itself: if $j$ is a descendant of $i$ there, then $i = j$.
