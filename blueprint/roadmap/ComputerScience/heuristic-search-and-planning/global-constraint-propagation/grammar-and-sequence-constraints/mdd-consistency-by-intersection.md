# MDD consistency by intersection with an exact MDD

One ordered MDD can be filtered against another on the same variable order by building their intersection: every arc of the first that lies on a path also represented in the second is kept, in time and space proportional to the number of nodes and arcs of the first times the width of the second. For SEQUENCE this makes MDD consistency fixed-parameter tractable in the window length.

Use [ordered MDDs and MDD consistency](mdd-consistency.md). Let $M$ and $M'$ be ordered MDDs on the same ordered variables $x_1,\dots,x_n$; $M'$ is **exact** for a constraint $C$ when its root-to-terminal paths are exactly the solutions of $C$. Say $M$ is MDD consistent *with respect to* $M'$ when every arc of $M$ lies on a root-to-terminal path of $M$ whose labels also form a path of $M'$; when $M'$ is exact for $C$ this is MDD consistency of $C$ on $M$. It requires a supporting path through each arc, not that every path of $M$ be a path of $M'$.

*The algorithm.* Build the intersection $I$ layer by layer: its nodes are pairs $(v,v')$ of nodes of $M$ and $M'$ in the same layer reached from the pair of roots, with an arc labelled $a$ from $(v,v')$ to $(\tilde v,\tilde v')$ whenever both $M$ and $M'$ have an arc labelled $a$ from $v$ to $\tilde v$ and from $v'$ to $\tilde v'$; then remove from $I$ the nodes and arcs on no path from its root to its terminal. Keep an arc of $M$ labelled $a$ out of $v$ exactly when some arc of $I$ labelled $a$ leaves a node $(v,v')$, and finally remove from $M$ all nodes and arcs on no root-to-terminal path.

**Theorem.**

1. The algorithm makes $M$ MDD consistent with respect to $M'$, removing exactly the arcs of $M$ on no path also represented in $M'$. Given adjacency lists for both diagrams and constant-time lookup of the outgoing arc of $M'$ with a given label at a node, it runs in $O(n+|V(M)|+|M|\cdot w(M'))$ time and space, where $|V(M)|$ and $|M|$ are the numbers of nodes and arcs of $M$ and $w(M')$ is the width of $M'$. The source states $O(|M|\cdot w(M'))$; this is the same bound when every layer of $M$ is nonempty and every node other than the root and the terminal has an incident arc.
2. For $C=\mathrm{Sequence}(X,q,l,u,S)$ and an MDD $M$ following the order of $X$, MDD consistency of $C$ on $M$ can therefore be established in $O(n+|V(M)|+|M|\,2^{q-1})$ time and space, given an exact MDD of $C$ of width $O(2^{q-1})$ (its construction not counted; Bergman, Cire and van Hoeve assert one of size $O(n2^{q-1})$ and use it with this width) and constant-time membership tests for $S$; in particular it is fixed-parameter tractable with respect to $q$.

## Depends on

- [MDD consistency](mdd-consistency.md): ordered MDDs, width, size and MDD consistency.
- [AMONG and SEQUENCE constraints](sequence-constraint.md): the constraint of item 2.

## Proof depends on

None.

## Expansion

*Item 1* is Theorem 2 of Bergman, Cire and van Hoeve. Correctness: a node $(v,v')$ of the trimmed intersection witnesses paths from the roots to $v$ and $v'$ with equal labels and, after trimming, equal-label continuations to the terminals; since labels out of a node are distinct, the kept arc of $M$ lies on a path whose labels also form a path of $M'$. Conversely an arc of $M$ on such a path gives a root-to-terminal path of $I$ through it. Cost: each arc of $M$ is compared with the outgoing arcs of at most $w(M')$ partner nodes, $I$ has $O(|M|\,w(M'))$ arcs, and scanning the $n+1$ layers and the node records of $M$ for the final trim adds $O(n+|V(M)|)$.

*Item 2* is Corollary 1. Obligation not expanded here: the existence of an exact MDD for SEQUENCE of size $O(n2^{q-1})$, which Bergman, Cire and van Hoeve attribute to van Hoeve et al.; van Hoeve, Pesant, Rousseau and Sabharwal's automaton reads the Boolean status sequence $[x_1\in S],[x_2\in S],\dots$, records the last $q$ status values, and its unfolded graph has $O(n2^q)$ vertices and arcs, which gives the same fixed-parameter conclusion with $2^q$ in place of $2^{q-1}$. In the intersection, a label $a$ of $M$ is looked up in the status diagram through $[a\in S]$, which is where the constant-time membership test is used.

## Sources

- D. Bergman, A. A. Cire and W.-J. van Hoeve, "MDD propagation for sequence constraints", *Journal of Artificial Intelligence Research* 50 (2014), 697–722, doi:10.1613/jair.4199. Algorithms 1–2 (Intersection, MDD-Consistency), Theorem 2 with proof and Corollary 1, §4, pp. 704–707.
- W.-J. van Hoeve, G. Pesant, L.-M. Rousseau and A. Sabharwal, "New filtering algorithms for combinations of among constraints", *Constraints* 14(2) (2009), 273–292, doi:10.1007/s10601-008-9067-7; author copy [https://www.andrew.cmu.edu/user/vanhoeve/papers/new_filtering.pdf](https://www.andrew.cmu.edu/user/vanhoeve/papers/new_filtering.pdf). The automaton for sequence recording the last $q$ values, with $O(n2^q)$ vertices and arcs, in the section on the reformulation as a regular constraint.
