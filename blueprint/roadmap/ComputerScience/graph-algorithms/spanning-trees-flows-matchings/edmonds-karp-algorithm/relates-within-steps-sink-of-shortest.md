# Distances to the sink do not decrease (abstract form of Edmonds–Karp, Proposition 3 (2))

Under the hypotheses of [the source version](relates-within-steps-source-of-shortest.md) ($p$ a shortest $r$-chain from $s$ to $t$, and every $r'$-step an $r$-step or the reverse of a step of $p$), every $r'$-walk of length $k$ from a vertex $u$ to $t$ can be replaced by an $r$-walk of length at most $k$ from $u$ to $t$; that is, $\delta_r(u, t) \le \delta_{r'}(u, t)$.

This is inequality (2) of Edmonds and Karp's Proposition 3, which they state with the remark that its proof is similar to that of (1). Here it is proved directly, by induction on the walk from its first step.

## Informally uses

- [A step of a chain splits it into two walks](exists-split-of-mem-path-edges.md): locates the reversed step on the shortest chain $p$.

## Sources

- J. Edmonds and R. M. Karp, "Theoretical improvements in algorithmic efficiency for network flow problems", *Journal of the ACM* 19(2) (1972), 248–264, §1.2 (Propositions 2 and 3, Lemmas 1 and 2, Theorem 1).
