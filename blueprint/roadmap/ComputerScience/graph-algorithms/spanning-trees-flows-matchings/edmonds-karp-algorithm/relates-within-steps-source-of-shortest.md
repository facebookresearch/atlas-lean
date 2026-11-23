# Distances from the source do not decrease (abstract form of Edmonds–Karp, Proposition 3 (1))

Let $r$ and $r'$ be relations on a set, and let $p$ be a shortest $r$-chain from $s$ to $t$: it has $L + 1$ entries and every $r$-walk from $s$ to $t$ has length at least $L$. Suppose every $r'$-step is an $r$-step or the reverse of a step of $p$. Then every $r'$-walk of length $k$ from $s$ to a vertex $u$ can be replaced by an $r$-walk of length at most $k$ from $s$ to $u$. Writing $\delta_r$ for walk distance (with $\delta = \infty$ when there is no walk), this says $\delta_r(s, u) \le \delta_{r'}(s, u)$ for every $u$.

With $r$ the residual network $N^k$, $p$ the shortest augmenting path $P^k$ and $r'$ the next residual network $N^{k+1}$, the hypothesis is Edmonds and Karp's Proposition 2 and the conclusion is inequality (1) of their Proposition 3. The proof follows theirs: along a shortest $r'$-walk, an $r$-step raises the $r$-distance by at most one, and the reverse of a step $(b, a)$ of $p$ lowers it by one, because $\delta_r(s, a) = \delta_r(s, b) + 1$ on a shortest path.

## Informally uses

- [A step of a chain splits it into two walks](exists-split-of-mem-path-edges.md): locates the reversed step on the shortest chain $p$.

## Sources

- J. Edmonds and R. M. Karp, "Theoretical improvements in algorithmic efficiency for network flow problems", *Journal of the ACM* 19(2) (1972), 248–264, §1.2 (Propositions 2 and 3, Lemmas 1 and 2, Theorem 1).
