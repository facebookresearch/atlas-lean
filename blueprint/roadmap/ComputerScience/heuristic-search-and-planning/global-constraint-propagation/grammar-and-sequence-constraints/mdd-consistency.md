# MDD consistency

An ordered multivalued decision diagram represents a set of assignments to a sequence of variables as the root-to-terminal paths of a layered graph; a constraint is MDD consistent on such a diagram when every arc lies on some path satisfying the constraint, which generalizes domain consistency.

Let $x_1,\dots,x_n$ be variables with finite domains $D(x_i)$.

- An **ordered MDD** $M$ is a directed acyclic multigraph whose nodes are partitioned into layers $L_1,\dots,L_{n+1}$, with $L_1=\{r\}$ (the root) and $L_{n+1}=\{t\}$ (the terminal); every arc goes from a node of some $L_i$ to a node of $L_{i+1}$ and carries a label in $D(x_i)$, and the labels of the arcs leaving one node are pairwise distinct. A path from $r$ to $t$ with labels $v_1,\dots,v_n$ represents the assignment $x_1=v_1,\dots,x_n=v_n$.
- The **size** $|M|$ is the number of arcs, and the **width** $w(M)$ is $\max_i|L_i|$.
- A path is **feasible** for a constraint $C$ on $x_1,\dots,x_n$ when its assignment satisfies $C$. $C$ is **MDD consistent** on $M$ when every arc of $M$ lies on some feasible path; establishing MDD consistency means removing all arcs on no feasible path.

Domain consistency ([generalized arc consistency](../generalized-arc-consistency.md)) of $C$ is MDD consistency on the width-one MDD with a single node $s_i$ per layer and arcs from $s_i$ to $s_{i+1}$ labelled by the values of $D(x_i)$.

## Depends on

- [Generalized arc consistency](../generalized-arc-consistency.md): the width-one special case.

## Proof depends on

None.

## Expansion

On the width-one MDD the root-to-terminal paths are exactly the tuples of $D(x_1)\times\dots\times D(x_n)$, so an arc labelled $a$ from $s_i$ lies on a feasible path iff $x_i=a$ has a support. In MDD-based constraint programming the width is capped by a fixed maximum, and MDD consistency is typically harder to establish than domain consistency: Andersen, Hadzic, Hooker and Tiedemann showed it NP-hard for ALLDIFFERENT, and Bergman, Cire and van Hoeve for SEQUENCE.

## Sources

- D. Bergman, A. A. Cire and W.-J. van Hoeve, "MDD propagation for sequence constraints", *Journal of Artificial Intelligence Research* 50 (2014), 697–722, doi:10.1613/jair.4199. §2 (ordered MDDs, size, width, feasible paths, MDD consistency, the width-one MDD) and §1.1 (the ALLDIFFERENT result of Andersen et al. 2007), pp. 699–701.
