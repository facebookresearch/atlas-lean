# Symmetric arc diagrams with crossings and base triples

**Setting.** Arc diagrams on nodes $1,\dots,n$ with no arc joining adjacent nodes model RNA structures beyond secondary structures.

- *Pseudoknot type.* $\mathcal P_n$: each node on at most one arc, arcs may cross (involutions of $[n]$ without transpositions $(i,i+1)$; a crossing is a $3412$ pattern). $P(n,k)$ counts those with exactly $k$ isolated nodes, so $P_n=\sum_kP(n,k)$ ($1,1,2,5,13,37,112,\dots$). A diagram is symmetric if its involution is invariant under reverse complement; $Q(n,k)$ counts symmetric diagrams with $k$ isolated nodes ($n\equiv k\pmod2$) and $Q_n=\sum_kQ(n,k)$ ($1,1,2,3,5,11,16,43,\dots$).
- *Bell type (base triples).* $\mathcal B_n$: arcs may cross and nonnesting arcs may share a node, i.e. set partitions of $[n]$ with no block containing consecutive integers, counted by the Bell number $B_{n-1}$. Such a diagram splits into arc-connected components (the blocks); it is symmetric if the partition is self-complementary under $j\mapsto n+1-j$. $A(n,k)$ counts symmetric diagrams with $k+1$ arc-connected components.

**Theorem 3.2.** For $n\ge3$, with $P(n,k)=0$ for $k<0$ or $k>n$,

$$
P(n,k)=(k+1)P(n-1,k+1)+P(n-1,k-1)-P(n-2,k).
$$

**Odd lengths (3.3).** $Q_{2n+1}=Q_{2n}+Q_{2n-1}$.

**Theorem 3.4.** For $n\ge3$ and $k$ even, with $Q(2n,k)=0$ for $k<0$ or $k>2n$,

$$
Q(2n,k)=(k+2)Q(2n-2,k+2)+Q(2n-2,k)+Q(2n-2,k-2)-Q(2n-4,k).
$$

**Theorem 5.1.** For $n\ge5$ and $2\le k\le n-3$,

$$
A(n,k)=k\,A(n-2,k)+A(n-2,k-1)+A(n-2,k-2),
$$

with $A(n,1)=1$, $A(n,n-1)=1$ and $A(n,n-2)=\lfloor(n-1)/2\rfloor$ for $n>1$. The totals $A_n=\sum_kA(n,k)$ begin $1,1,2,3,7,12,31,59,164,\dots$; numerically the fraction of symmetric diagrams in these two families decays even faster than for secondary structures.

## Expansion

For $P(n,k)$, diagrams split into three disjoint classes: the first node is isolated; the first node lies on an arc and the second node is free; neither of the first two nodes is isolated. Deleting or re-attaching the first node maps each class onto diagrams with $n-1$ or $n-2$ nodes, giving the three terms. For symmetric diagrams the same surgery is performed simultaneously at both ends, on the first and last nodes as a mirror pair, which changes $n$ by two. A symmetric odd diagram has an isolated middle node, whose two neighbors are either joined by a short arc or not. For Bell-type diagrams the classes are: first and last nodes isolated; first and last nodes joined by a single arc; first node joined to a node other than the last.

## Sources

- Juan B. Gil and Luis E. Lopez, "Enumeration of symmetric arc diagrams", arXiv (2022), Section 3 "Symmetric arc diagrams with crossings" (Theorem 3.1 quoted from Hardin and Sloane, Theorem 3.2, equation (3.3), Theorem 3.4), Section 5 "Symmetric arc diagrams of Bell type" (Theorem 5.1) and Section 6 "Final remarks", <https://doi.org/10.48550/arXiv.2203.10589> Published version: Involve 16 (2023) 107-126, <https://doi.org/10.2140/involve.2023.16.107>.
