# Monotonicity and termination of irreversible threshold processes

Let $G$ be a finite graph on $n$ vertices with nonnegative edge weights $w_{uv}$ and thresholds $\theta_v$, and let $F(A) = A \cup \{v : \sum_{u \in A}w_{uv} \ge \theta_v\}$, a monotone map on vertex sets. Starting from $A_0$, the synchronous process $A_{t+1} = F(A_t)$ satisfies $A_0 \subseteq A_1 \subseteq \cdots$ and is constant from some $t \le n$ on, at the least fixed point of $F$ containing $A_0$. Here the least fixed point of $F$ containing $A_0$ is the least fixed point of the monotone map $H(B) = A_0 \cup F(B)$ on subsets of the $n$ vertices, which is $H^n(\emptyset)$: it is a fixed point of $H$ and lies in every $B$ with $H(B) \subseteq B$; each $A_t$ lies in it by induction, and the stable value of $(A_t)$ is a fixed point of $F$ containing $A_0$, hence a set with $H(B) \subseteq B$. Any asynchronous schedule that activates one eligible vertex at a time, and eventually activates every vertex that stays eligible, stops at the same set. Processes with negative weights or deactivation need not be monotone and are not covered.

## Proof depends on

- [Finite iteration from the empty set reaches a fixed point](../../Order/fixed-points-domain-theory/least-and-greatest-fixed-points-on-finite-sets/lfp-fin-fixed.md): the finite iterate $H^n(\emptyset)$ is a fixed point of $H$.
- [The finite least fixed point lies in every pre-fixed point](../../Order/fixed-points-domain-theory/least-and-greatest-fixed-points-on-finite-sets/lfp-fin-le.md): the finite iterate lies in every set $B$ with $H(B) \subseteq B$.

## Sources

- D. Easley and J. Kleinberg, *Networks, Crowds, and Markets*, Cambridge University Press, 2010, Section 19.3, cascades and clusters, <https://www.cs.cornell.edu/home/kleinber/networks-book/networks-book.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
