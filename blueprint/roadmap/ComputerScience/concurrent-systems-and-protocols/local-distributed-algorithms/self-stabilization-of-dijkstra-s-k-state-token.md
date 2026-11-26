# Self-stabilization of Dijkstra's token ring

Consider $n$ processes $0, \dots, n - 1$ on a unidirectional ring. Each process $i$ can observe its own state and that of its predecessor $i - 1 \bmod n$, and each process has a state $\ell_i \in \mathbb{Z}_{n+1}$. Steps are taken one at a time by an adversarial scheduler, the central daemon, and only enabled commands may be executed. Dijkstra's token ring algorithm has two commands:

- process $0$: if $\ell_0 = \ell_{n-1}$, set $\ell_0 \leftarrow \ell_{n-1} + 1 \bmod (n + 1)$;
- process $i \ne 0$: if $\ell_i \ne \ell_{i-1}$, set $\ell_i \leftarrow \ell_{i-1}$.

A process holds a token exactly when its command is enabled.

1. **At least one token.** In every configuration some process holds a token. If no nonzero process has one, all states are equal, and then process $0$ has one.
2. **Closure.** Call a configuration *legal* if, for some $j$, $\ell_i=\ell_0$ for all $i\le j$ and $\ell_i=\ell_0-1$ modulo $n+1$ for all $i>j$. A legal configuration has exactly one token and every step from it is legal. Unique privilege alone is weaker: it allows a constant configuration or two constant blocks of distinct colors, not necessarily consecutive colors.
3. **Convergence.** From an arbitrary configuration of a nonempty ring, every execution of at least $2n^2$ actual steps visits a legal configuration within its first $2n^2$ steps. This bound does not require scheduler fairness. In particular the ring has exactly one token at the end of this prefix.

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

- J. Aspnes, *Notes on Theory of Distributed Systems*, Yale University, <https://cs.yale.edu/homes/aspnes/classes/4650/notes.pdf>, Chapter 32: Section 32.1 (guarded commands, the central and distributed daemons) and Section 32.2 (Algorithm 32.1, the token rule, legal configurations, Lemma 32.2.1 and the potential-function proof of stabilization in $O(n^2)$ steps).
- E. W. Dijkstra, "Self-stabilizing systems in spite of distributed control", *Communications of the ACM* 17(11):643–644, 1974.
