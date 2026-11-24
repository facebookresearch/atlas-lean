# Endpoint-aware modulus w'_T of finite-valued cadlag paths

Let $(E,r)$ be a metric space, $T>\delta>0$ and $x:[0,T]\to E$ càdlàg. For an interval $I$ write $\operatorname{osc}(x,I)=\sup_{s,t\in I}r(x(s),x(t))$. Define

$$w'_T(x,\delta)=\inf\ \max\Bigl(\max_{1\le i<k}\operatorname{osc}\bigl(x,[t_{i-1},t_i)\bigr),\ \operatorname{osc}\bigl(x,[t_{k-1},T]\bigr)\Bigr),$$

the infimum over partitions $0=t_0<t_1<\dots<t_k=T$ with $t_i-t_{i-1}>\delta$ for every $i$, including $i=k$; the partition $\{0,T\}$ is admissible because $T>\delta$. The last interval is closed, so a jump at $T$ counts.

**Lemma.** Let $E$ be a finite metric space, put $\rho=\min\{r(a,b):a\ne b\in E\}$, and let $J\subseteq(0,T]$ be the (finite) set of jump times of $x$. Then $w'_T(x,\delta)=0$ if and only if $J\subseteq(\delta,T-\delta)$, consecutive points of $J$ are more than $\delta$ apart, and $x$ has no jump at $T$ (the last condition is part of the first). Otherwise $w'_T(x,\delta)\ge\rho$.

Examples: for $E=\{0,1\}$ with $r(0,1)=1$, a single jump at $s\in(\delta,T-\delta)$ gives $w'_T=0$; on $T=3$ the pulse $\mathbf 1_{[1,1+1/m)}$ has $w'_3\ge1$ once $1/m\le\delta$; and for $T=1$, $\delta=1/5$ and $x=\mathbf 1_{\{t\ge9/10\}}$, $9/10\notin(1/5,4/5)$, so $w'_1(x,1/5)=1$, not $0$.

## Depends on

- [Skorokhod space D([0,T],E) for a metric space E: J1 topology and embeddings](skorokhod-space-d-0-t-e-for-a-metric-space-e-j1.md)

## Expansion

A proof page must establish: a path with finitely many jumps has zero oscillation on $[a,b)$ exactly when it has no jump in $(a,b)$, and on $[a,T]$ exactly when it has no jump in $(a,T]$; the partition formed by $0$, the jump times and $T$ is admissible under the stated conditions; conversely any partition with all oscillations zero has every jump time among $t_1,\dots,t_{k-1}$, which forces the conditions; and since every oscillation of a finite-valued path is $0$ or at least $\rho$, the infimum is $0$ or at least $\rho$. The three examples should be checked.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), Chapter 3 (the modulus $w'$ of the Skorokhod topology; the endpoint-aware variant on a compact interval is the one defined above).
