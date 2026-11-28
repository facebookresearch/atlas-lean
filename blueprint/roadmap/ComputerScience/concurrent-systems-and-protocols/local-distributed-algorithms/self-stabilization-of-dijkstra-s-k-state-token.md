# Self-stabilization of Dijkstra's token ring

Consider $n \ge 1$ processes $0, \dots, n - 1$ on a unidirectional ring. Each process $i$ can observe its own state and that of its predecessor $i - 1 \bmod n$, and each process has a state $\ell_i \in \mathbb{Z}_{n+1}$. Steps are taken one at a time by an adversarial scheduler, the central daemon, and only enabled commands may be executed. Dijkstra's token ring algorithm has two commands:

- process $0$: if $\ell_0 = \ell_{n-1}$, set $\ell_0 \leftarrow \ell_{n-1} + 1 \bmod (n + 1)$;
- process $i \ne 0$: if $\ell_i \ne \ell_{i-1}$, set $\ell_i \leftarrow \ell_{i-1}$.

A configuration is in [consecutive-color legal form](piecewise-legal.md) if there is a cut $0 \le j < n$ with $\ell_i=\ell_0$ for all $i\le j$ and $\ell_i=\ell_0-1$ modulo $n+1$ for all $i>j$. The second block may be empty.

1. **[Convergence](exists-piecewise-legal-of-steps.md).** Every prefix of $2n^2$ actual steps, from any initial configuration, visits a legal configuration no later than the end of the prefix. No scheduler fairness is needed.
2. **[Closure](piecewise-legal-closed.md).** Every actual step from a legal configuration leads to a legal configuration.

A process holds a token exactly when its command is enabled. The [legal-form characterization](piecewise-legal-iff.md) implies that a legal configuration has exactly one token. Unique privilege alone is weaker: two constant blocks need not have consecutive colors.

**Proof of closure.** From a constant configuration only process $0$ moves. Its increment makes the old color one less than the new first color, even when the color wraps around; in a singleton ring the result is still constant. With a nonempty second block, only process $j+1$ can move. It copies the first block's color, advancing the cut by one. When it is the last process, the result is constant and the privilege returns to process $0$.

**Proof of convergence.** Some color $c$ is missing initially, since there are $n+1$ colors and $n$ processes. Until the first constant configuration, the processes of color $c$ form an initial segment of the order $0,\ldots,n-1$: the color can only be introduced by process $0$, and the copying rule propagates it to the right. If this segment reaches process $n-1$, the configuration is constant and hence legal.

Before a constant configuration is reached, use the potential

$$
n\bigl((c-\ell_0)\bmod(n+1)\bigr)
    + \sum_{\substack{1\le i<n\\ \ell_i\ne\ell_{i-1}}}(n-i),
$$

where the modular difference takes its least nonnegative representative. A copying step removes a disagreement of weight $n-i$ at process $i$ and can add one only at process $i+1$, of smaller weight. If process $0$ increments, its old color cannot equal $c$: the enabling equality would put color $c$ at the last process as well. The modular distance then drops by one without wrapping. The resulting decrease of $n$ outweighs any new disagreement, whose weight is at most $n-1$. The initial potential is at most $n^2+n(n-1)<2n^2$, so a prefix of $2n^2$ steps cannot avoid visiting a constant configuration.

Dijkstra's paper also gives the general $K$-state version and variants using fewer states. The bound here is for the alphabet of size $n+1$ only.

## Background

- [Dijkstra's token ring never deadlocks](../dijkstra-s-self-stabilizing-token-ring/exists-privileged.md)
- [Configurations with one privilege are closed](../dijkstra-s-self-stabilizing-token-ring/legit-closed.md)

## Sources

- J. Aspnes, *Notes on Theory of Distributed Systems*, Yale University, [Chapter 32, §32.2](https://www.cs.yale.edu/homes/aspnes/classes/4650/notes.pdf) (Algorithm 32.1, the consecutive-color legal form and its closure, and the quadratic convergence argument).
- E. W. Dijkstra, ["Self-stabilizing systems in spite of distributed control"](https://www.cs.utexas.edu/~EWD/transcriptions/EWD04xx/EWD426.html), *Communications of the ACM* 17(11):643–644, 1974 (original transition rules).
