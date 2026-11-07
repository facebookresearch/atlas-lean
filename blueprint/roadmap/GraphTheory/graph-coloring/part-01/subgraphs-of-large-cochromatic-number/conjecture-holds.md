# Alon–Krivelevich–Sudakov theorem on subgraphs of large cochromatic number

There is a real
number $c > 0$ such that for every simple graph $G$ on a finite vertex set with chromatic number
$m$ there are a subgraph $H$ of $G$ and a natural number $k$ with $k \ge c\,m / \log m$ such that
the cochromatic number of $H$ is at least $k$. Moreover, there is a real number $c > 0$ with the
same property for the bound $k \ge c\sqrt{m / \log m}$.

Here $\log$ is the natural logarithm, with the conventions $\log 0 = 0$ and $x / 0 = 0$, so both
bounds are $0$ when $m \le 1$. This answers Erdős Problem 760 affirmatively.

## Sources

- plby/lean-proofs, src/v4.29.1/ErdosProblems/Erdos760.lean (theorem erdos_760, following Alon, Krivelevich and Sudakov, Subgraphs with a large cochromatic number, 1997), pinned revision 8822f7ddef30fadbd92e1c6ab4ed897af356af5e, https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/v4.29.1/ErdosProblems/Erdos760.lean#L1306. Moved from `OpenConjectures/Combinatorics/ErdosProblem760`.
