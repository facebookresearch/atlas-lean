# Quartet systems displayed by level-1 networks

Let $N$ be a binary level-1 network on $X$, $|X| \ge 4$. A quartet $ab|cd$ is **displayed** by $N$ if $N$ contains two vertex-disjoint paths, one joining $a$ and $b$ and one joining $c$ and $d$; write $\mathcal{Q}(N)$ for the displayed quartets. For a quartet system $\mathcal{Q}$ and a 4-subset $Y$, let $m_{\mathcal{Q}}(Y)$ be the number of quartets of $\mathcal{Q}$ on $Y$; $\mathcal{Q}$ is **dense** if $m_{\mathcal{Q}}(Y) \ge 1$ for all $Y$, and a quartet is **distinguished** in $\mathcal{Q}$ if it is the only quartet of $\mathcal{Q}$ on its support. A network is **3-cycle free** if it has no cycle with three vertices.

**Theorem 3.** A dense quartet system $\mathcal{Q}$ on $X$ satisfies $\mathcal{Q} = \mathcal{Q}(N)$ for some binary level-1 network $N$ if and only if

- (D1) $m_{\mathcal{Q}}(Y) \in \{1, 2\}$ for every $Y \in \binom{X}{4}$;
- (D2) for distinct $a, b, c, d, x$, if $\{ab|cd,\ ad|bc,\ ax|cd,\ ac|xd\} \subseteq \mathcal{Q}$ then $\{ab|dx,\ bd|ax\} \subseteq \mathcal{Q}$;
- (D3) if $ab|cd$ is distinguished in $\mathcal{Q}$, then for each $x \in X \setminus \{a, b, c, d\}$, $ax|cd$ or $ab|cx$ is distinguished in $\mathcal{Q}$.

If (D1)–(D3) hold, there is a unique 3-cycle-free level-1 network $N$ with $\mathcal{Q}(N) = \mathcal{Q}$.

## Depends on

- [Quarnet systems of level-1 networks](quarnet-systems-of-level-1-networks.md)

## Expansion

A 4-subset restricted to a level-1 network either sees a cut-edge separating two pairs, giving one displayed quartet, or sits on a 4-cycle $a \oplus b \oplus c \oplus d$, which displays exactly the two quartets $ab|cd$ and $ad|bc$ compatible with the cyclic order; hence (D1). Distinguished quartets correspond to cut-edge splits, so (D3) is the tree saturation condition applied to them, and (D2) transfers cyclic orders across overlapping 4-subsets, the quartet shadow of cyclativity. Translating quartets back into qnets reduces the statement to the quarnet characterization; 3-cycles are invisible to quartets (and to quarnets of most types), which is why uniqueness holds only among 3-cycle-free networks.

## Sources

- K. T. Huber, V. Moulton, C. Semple, T. Wu, "Quarnet inference rules for level-1 networks", Bulletin of Mathematical Biology (2018), Section 4, Theorem 3, <https://doi.org/10.1007/s11538-018-0450-2> (PMC6061523).
