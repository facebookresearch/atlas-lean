# Self-stabilization of Dijkstra's token ring

Consider $n$ processes $0, \dots, n - 1$ on a unidirectional ring. Each process $i$ can observe its own state and that of its predecessor $i - 1 \bmod n$, and each process has a state $\ell_i \in \mathbb{Z}_{n+1}$. Steps are taken one at a time by an adversarial scheduler, the central daemon, and only enabled commands may be executed. Dijkstra's token ring algorithm has two commands:

- process $0$: if $\ell_0 = \ell_{n-1}$, set $\ell_0 \leftarrow \ell_{n-1} + 1 \bmod (n + 1)$;
- process $i \ne 0$: if $\ell_i \ne \ell_{i-1}$, set $\ell_i \leftarrow \ell_{i-1}$.

A process holds a token exactly when its command is enabled.

1. **At least one token.** In every configuration some process holds a token. If no nonzero process has one, all states are equal, and then process $0$ has one.
2. **Closure.** Call a configuration *legal* if, for some $j$, $\ell_i = \ell_j$ for all $i \le j$ and $\ell_i = \ell_j - 1 \pmod{n+1}$ for all $i > j$. Every legal configuration has exactly one token, and every step from a legal configuration leads to a legal configuration.
3. **Convergence.** From an arbitrary configuration, every execution reaches a legal configuration within $O(n^2)$ steps.

**Proof of convergence.** Some value $c$ is missing from the initial configuration, by the pigeonhole principle. By induction, every non-legal reachable configuration has the form $\ell_i = c$ exactly for $i < j$, for some $0 \le j < n$: the value $c$ can only enter at process $0$ and then spread along the ring. A potential function combining $(c - \ell_0) \bmod (n + 1)$ with the positions of the processes out of step drops by at least $1$ at every step of a non-legal execution. It starts at $O(n^2)$.

Dijkstra's paper also gives the general $K$-state version, with states in $\mathbb{Z}_K$, reported to stabilize under the central daemon when $K$ is at least the number of machines, together with variants using fewer states. That general condition is not proved here.

## Proof depends on

- [Dijkstra's token ring never deadlocks](../dijkstra-s-self-stabilizing-token-ring/exists-privileged.md)
- [Legitimate configurations of Dijkstra's token ring are closed](../dijkstra-s-self-stabilizing-token-ring/legit-closed.md)

## Sources

- J. Aspnes, *Notes on Theory of Distributed Systems*, Yale University, <https://cs.yale.edu/homes/aspnes/classes/4650/notes.pdf>, Chapter 32: Section 32.1 (guarded commands, the central and distributed daemons) and Section 32.2 (Algorithm 32.1, the token rule, legal configurations, Lemma 32.2.1 and the potential-function proof of stabilization in $O(n^2)$ steps).
- E. W. Dijkstra, "Self-stabilizing systems in spite of distributed control", *Communications of the ACM* 17(11):643–644, 1974.
