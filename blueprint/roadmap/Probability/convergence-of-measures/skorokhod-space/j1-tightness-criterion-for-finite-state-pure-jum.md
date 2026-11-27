# J1 tightness criterion for finite-state pure-jump processes (jump separation)

Let $E$ be a finite set with the discrete metric, and let $X^m$, $m\ge1$, and $X$ be processes with paths in $D([0,\infty),E)$ (pure-jump paths with finitely many jumps on bounded intervals). Let $T_0\subseteq[0,\infty)$ be dense with $0\in T_0$. Assume:

- the finite-dimensional distributions of $X^m$ at every finite set of times in $T_0$ converge to those of $X$;
- $X$ is stochastically continuous at every $t\in T_0$: $P(X_{t-}\ne X_t)=0$;
- the jump-separation condition (b) of the [sufficient criterion for tightness](sufficient-criterion-for-relative-compactness-an.md): for an unbounded set $H$ of horizons, $\lim_{\delta\to0}\limsup_mP\bigl(w'_T(X^m,\delta)>0\bigr)=0$ for every $T\in H$.

Then $X^m\to X$ in law in $D([0,\infty),E)$ with the J1 topology. The finite-dimensional distributions identify the limit because they [determine laws on $D$](borel-sigma-algebra-of-d-equals-the-coordinate-s.md).

The jump-separation condition cannot be dropped. The deterministic pulses $x_m=\mathbf 1_{[1,1+1/m)}$ have at most two jumps each but violate it, and do not converge in J1. The randomly translated pulse $\mathbf 1_{[U,U+1/m)}$ with $U$ uniform on $[1,2]$ has finite-dimensional distributions converging to those of $0$ at every time, but does not converge in law to $0$; it also violates the condition. Two jumps whose times merge in the limit (for instance two successive merger events of a coalescent approximation at distance $1/m$) violate it as well.

## Depends on

- [Sufficient criterion for relative compactness and tightness in D([0,infinity),E), finite E](sufficient-criterion-for-relative-compactness-an.md)
- [Borel sigma-algebra of D equals the coordinate sigma-algebra; fdd determine laws](borel-sigma-algebra-of-d-equals-the-coordinate-s.md)

## Proof depends on

- [Prokhorov's theorem: tight sets of probability measures are relatively compact](../prokhorov-theorem-on-a-polish-space.md)

## Expansion

A proof page must establish: tightness from the jump-separation condition; Prokhorov's theorem on the Polish space $D([0,\infty),E)$, so that every subsequence has a further subsequence converging in law to some $Y$; equality of the finite-dimensional distributions of $Y$ and $X$ at the times of $T_0$ that are not fixed discontinuities of $Y$, which are dense; determination of the law by those times, where the cited determination on $[0,T]$ must be transferred to $[0,\infty)$ through restriction maps; and the three counterexamples.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), Chapter 3 (Skorokhod topology; convergence in distribution in $D_E[0,\infty)$).
