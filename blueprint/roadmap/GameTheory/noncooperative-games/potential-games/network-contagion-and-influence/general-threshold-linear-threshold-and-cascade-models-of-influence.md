# General threshold, linear threshold and cascade models of influence

On a finite directed graph, a *general threshold model* gives each vertex $v$ a monotone function $g_v$ on subsets of its in-neighbours with $g_v(\emptyset) = 0$ and values in $[0, 1]$; thresholds $\theta_v$ are drawn independently and uniformly from $[0, 1]$, and starting from a seed set, $v$ becomes active once $\theta_v \le g_v(\text{active in-neighbours})$. The *linear threshold model* has $g_v(A) = \sum_{u \in A} w_{uv}$ with $\sum_u w_{uv} \le 1$. In an *(order-independent) cascade model*, each newly active $u$ gets one chance to activate $v$ with probability depending on the set of $v$'s neighbours that already tried; the *independent cascade model* uses fixed edge probabilities. The *influence* $\sigma(S)$ is the expected number of active vertices at the end.

## Depends on

- [Submodular set function](../../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Sources

- David Kempe, Jon Kleinberg and Eva Tardos, "Maximizing the Spread of Influence through a Social Network", Proceedings of the Ninth ACM SIGKDD International Conference on Knowledge Discovery and Data Mining, 2003.
- David Kempe, Jon Kleinberg and Eva Tardos, "Influential Nodes in a Diffusion Model for Social Networks", Automata, Languages and Programming (ICALP 2005), 2005.
- Jon Kleinberg, "Cascading Behavior in Networks: Algorithmic and Economic Issues", Algorithmic Game Theory, Cambridge University Press, 2007.
