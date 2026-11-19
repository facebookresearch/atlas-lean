# Admixture graph

An admixture graph on a set $V$ of nodes (populations) consists of a root $\rho \in V$, a finite set $\mathrm{pa}(X) \subseteq V$ of parents for each node $X$, and real admixture proportions $a(X, Y)$ for $X, Y \in V$, such that

- the root has no parent, and every other node has one parent (a tree node) or two parents (an admixture node);
- $a(X, Y) \ge 0$ for all $X, Y$, and $a(X, Y) = 0$ when $Y \notin \mathrm{pa}(X)$;
- $\sum_{Y \in \mathrm{pa}(X)} a(X, Y) = 1$ for every node $X \ne \rho$;
- the graph is acyclic: there is no infinite sequence $X_0, X_1, \dots$ with $X_{i+1} \in \mathrm{pa}(X_i)$ for all $i$.

Here $a(X, Y)$ is the probability that a lineage in $X$ descends from the parent $Y$ (Patterson et al. 2012).

## Sources

- N. Patterson, P. Moorjani, Y. Luo, S. Mallick, N. Rohland, Y. Zhan, T. Genschoreck, T. Webster, D. Reich, *Ancient admixture in human history*, Genetics 192 (2012), 1065–1093, Appendix.
