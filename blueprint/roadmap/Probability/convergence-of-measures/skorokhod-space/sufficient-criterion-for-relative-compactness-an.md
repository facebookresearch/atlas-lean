# Sufficient criterion for relative compactness and tightness in D([0,infinity),E), finite E

Let $E$ be a finite metric space and give $D([0,\infty),E)$ the local J1 (Skorokhod) topology. Let $w'_T$ be the [endpoint-aware modulus](endpoint-aware-modulus-w-t-of-finite-valued-cadl.md), applied to the restriction of a path to $[0,T]$, and let $H\subseteq(0,\infty)$ be an unbounded set of horizons.

(a) **Deterministic, sufficient direction.** If $A\subseteq D([0,\infty),E)$ satisfies $\lim_{\delta\to0}\sup_{x\in A}w'_T(x,\delta)=0$ for every $T\in H$, then $A$ is relatively compact. Compact containment is automatic because $E$ is finite.

(b) **Probabilistic, sufficient direction.** If processes $X^m$ with paths in $D([0,\infty),E)$ satisfy $\lim_{\delta\to0}\limsup_{m\to\infty}P\bigl(w'_T(X^m,\delta)>0\bigr)=0$ for every $T\in H$, then the laws of $(X^m)$ are tight.

No converse is claimed: with $E=\{0,1\}$, the family $\{\mathbf 1_{\{t\ge s\}}:s\ge1\}\cup\{0\}$ is compact, yet $\sup_xw'_T(x,\delta)=1$ for every $T\ge1$ and every $\delta$, because the path jumping at $s=T$ has a jump at the horizon.

## Depends on

- [Endpoint-aware modulus w'_T of finite-valued cadlag paths](endpoint-aware-modulus-w-t-of-finite-valued-cadl.md)

## Proof depends on

- [D([0,T],E) is Polish for Polish E](d-0-t-e-is-polish-for-polish-e.md)

## Expansion

A proof page must establish:

- that $w'_T(x,\delta)=0$ forces the Ethier–Kurtz modulus $w'(x,\delta,S)$ to vanish for every $S\le T$, so the hypothesis of (a), holding on an unbounded set of horizons, gives their relative compactness criterion for all horizons;
- (b) from (a) and the corresponding tightness criterion, using that $\{w'_T(\cdot,\delta)=0\}$ is the relevant event because the modulus of a finite-valued path is $0$ or at least the minimal distance;
- that separated jumps, with no jump at the horizon, give $w'_T=0$ on the event; that a pulse of width $1/m$ violates the hypothesis of (b); and the compact family above, showing that no converse holds.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), Chapter 3 (relative compactness and tightness in $D_E[0,\infty)$).
