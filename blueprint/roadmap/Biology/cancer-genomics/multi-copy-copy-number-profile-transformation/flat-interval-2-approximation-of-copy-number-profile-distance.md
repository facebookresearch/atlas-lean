# Flat-interval 2-approximation of copy-number profile distance

**Setting.** For copy-number profiles $u,v\in\mathbb N^n$ with segmental events $(s,t,\delta)$ and a unit-cost function $f$ (every allowed event costs 1), let $d_f(u,v)$ be the minimum number of events transforming $u$ into $v$. Put $w=u-v$, extended by $w_0=w_{n+1}=0$. An interval $[a,b]\subseteq[0,n+1]$ is *flat* if $w$ is constant on it; let $F_w$ be the set of maximal flat intervals, which partitions $[0,n+1]$. The two intervals containing $0$ and $n+1$ are the extreme flat intervals (value $0$).

**Lemma (flat-interval lower bound).** If $u\ne v$ and neither has a null position, then for every unit-cost $f$

$$d_f(u,v)\ \ge\ \left\lceil\frac{|F_w|-1}{2}\right\rceil .$$

**Theorem.** For the unconstrained cost function $f=\mathrm{any}$ and CNPs with no null positions, returning $|F_w|-2$ approximates $d_{\mathrm{any}}(u,v)$ within a factor 2, and $F_w$ is computed in one linear pass over $w$.

**Null positions.** If $v_i=v_{i+1}=0$, deleting whichever of positions $i,i+1$ has the smaller value in $u$ preserves $d_f$; if $v_i=0$ and $w_{i-1}\ge w_i$ or $w_{i+1}\ge w_i$, deleting position $i$ preserves $d_f$, for every unit-cost $f$.

## Expansion

Positions in one flat interval need the same net change, so they can always be moved together. Intuitively, each event has two endpoints and so can remove only a bounded number of the $|F_w|-1$ boundaries between flat intervals, all of which must disappear when $u$ reaches $v$; the formal proof of the lower bound is in the supplementary material of the source. Under $\mathrm{any}$, one event per non-extreme flat interval, with $\delta$ equal to minus its $w$-value and with amplifications first so no position hits zero, realizes $|F_w|-2$ events, at most twice the bound. The bound is tight up to the constant: for $w=(1,2,\dots,k,\dots,2,1)$ one can remove two boundaries per event. The null-position rules shrink an instance before applying the approximation.

## Depends on

- [Strong NP-hardness of the copy-number profile transformation problem](strong-np-hardness-of-copy-number-profile-transformation.md)

## Sources

- G. Cordonnier, M. Lafond, "Comparing copy-number profiles under multi-copy amplifications and deletions", *BMC Genomics* 21(Suppl 2):198 (2020), Lemmas 3, 4 and 5, Theorem 2, <https://doi.org/10.1186/s12864-020-6611-3>, PMCID: PMC7160889.
