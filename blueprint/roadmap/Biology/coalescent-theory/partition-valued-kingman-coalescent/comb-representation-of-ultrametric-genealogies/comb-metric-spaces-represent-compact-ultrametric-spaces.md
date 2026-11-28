# Comb representation of compact ultrametric spaces

**Combs and comb metrics.** Let $I$ be a compact interval. A **comb** is a function $f:I\to[0,\infty)$ such that $\{f\ge\varepsilon\}$ is finite for every $\varepsilon>0$. For $s,t\in I$ put

$$
d_f(s,t)=\sup_{(s\wedge t,\;s\vee t)}f .
$$

Then $d_f$ is an ultrametric pseudo-distance on $\{f=0\}$, i.e. $d_f(r,t)\le\max(d_f(r,s),d_f(s,t))$; let $\dot I$ be the quotient of $\{f=0\}$ by $d_f(s,t)=0$. To complete it, give each $t\in I$ a left face $(t,l)$ and a right face $(t,r)$ and set, for $s<t$,

$$
d_f((s,r),(t,l))=\sup_{(s,t)}f,\quad d_f((s,l),(t,l))=\sup_{[s,t)}f,\quad d_f((s,r),(t,r))=\sup_{(s,t]}f,\quad d_f((s,l),(t,r))=\sup_{[s,t]}f,
$$

with $d_f((t,l),(t,r))=f(t)$; the two faces are identified when $f(t)=0$. The quotient $\bar I$ of $I\times\{l,r\}$ by zero distance is the **comb metric space** of $f$.

**Proposition.** $(\bar I,d_f)$ is a compact ultrametric space.

**Theorem (converse).** Let $(U,d)$ be a compact ultrametric space carrying a finite measure $\mu$ of total mass $m$ that has no atom and charges every ball of positive radius, and let $I=[0,m]$. Then there exist a comb $f$ on $I$ and a global isometry $\bar\phi:(\bar I,d_f)\to(U,d)$ that maps Lebesgue measure on $I$ to $\mu$. In particular, every compact ultrametric space without isolated points is isometric to a comb metric space (take $\mu$ to be the visibility measure, which splits mass equally among sub-balls at each branching).

In genealogical terms, an ultrametric space is the set of leaves of a dated tree with $d(x,y)=2\times$(time to the most recent common ancestor); a comb lists the leaves in a planar order and records, between consecutive leaves, the coalescence depth, exactly as for a finite ordered sample $x_1,\dots,x_n$ with $f=\sum_{i=1}^{n-1}d(x_i,x_{i+1})\mathbf 1_{\{i\}}$. For example, if $f=\sum_j\tau_j\mathbf 1_{\{U_j\}}$ with $(U_j)$ i.i.d. uniform on $(0,1)$ and $\tau_j=\sum_{k\ge j+1}e_k$, $e_k$ independent exponential with rate $k(k-1)/2$, then the partitions of i.i.d. uniform points $V_i$ induced by $d_f(V_i,V_j)\le t$ form a Kingman coalescent.

## Depends on

- [Ultrametric on taxa](../../../phylogenetics/splits-compatibility-ultrametrics-and-upgma/is-ultrametric.md)
- [Kingman's coalescent on the natural numbers](../kingman-coalescent-on-n-as-a-time-indexed-cadlag.md)

## Proof depends on

- [Ultrametrics are dated tree metrics](../../../phylogenetics/splits-compatibility-ultrametrics-and-upgma/is-ultrametric-iff-is-dated-tree-metric.md)

## Expansion

Compactness: given a sequence in $\bar I$, extract a monotone subsequence of its projections to $I$; since $\{f\ge\varepsilon\}$ is finite, the supremum of $f$ over the shrinking gap tends to $0$, so the sequence converges to the left face of the limit point (increasing case) or the right face (decreasing case).

Converse: for $t>0$ the relation $d(x,y)\le t$ partitions $U$ into closed balls of radius $t$; compactness makes each partition finite, and the partitions refine as $t\downarrow0$ at a sequence of jump times $t_0>t_1>\cdots\to0$. Order the balls consistently (children replace parents in the ordered list) and lay them down as consecutive intervals of lengths $\mu(B)$ in $[0,m]$. Each boundary point $a$ between intervals is created at a unique jump time $t_n$; set $f(a)=t_n$ and $f=0$ elsewhere. A point $r$ with $f(r)=0$ lies in a nested sequence of intervals whose balls shrink to a single point $\phi(r)$, and $d_f(r,s)\le t$ iff no boundary created at level above $t$ separates $r$ and $s$ iff $\phi(r),\phi(s)$ share a ball of radius $t$. So $\phi$ is an isometry pushing Lebesgue measure to $\mu$; it extends to the completion, and surjectivity follows because $\mu$ charges every ball.

## Sources

- Amaury Lambert and Gerónimo Uribe Bravo, *The comb representation of compact ultrametric spaces*, p-Adic Numbers Ultrametric Anal. Appl. 9(1) (2017), 22–38. <https://doi.org/10.1134/S2070046617010034> Section 2 (Definition 2.1, the Kingman-coalescent example, Definition 2.2, Proposition 2.3, Definition 2.4), Theorem 3.1 and the remark following its proof. Locators use the numbering of the preprint arXiv:1602.08246.
