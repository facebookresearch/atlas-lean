# Characterizations of acyclic database schemas

Let $R_1,\ldots,R_n$ be distinct nonempty finite sets of named attributes, with $n\geq 1$.
The vertices of the schema hypergraph are the attributes in their union; its edges are the schemes $R_i$.
An instance gives each $R_i$ a finite set $I_i$ of tuples defined exactly on $R_i$, with values in $\mathbb{N}$.
Its full natural join $J$ consists of the tuples on the union whose restriction to each $R_i$ belongs to $I_i$.

The following are equivalent:

1. Every pairwise consistent instance is globally consistent. Pairwise means $\pi_{R_i}(I_i\bowtie I_j)=I_i$ for every ordered pair $i,j$;
   global means $\pi_{R_i}(J)=I_i$ for every $i$. Thus each local tuple must extend to **one** tuple satisfying all the relations at once.
2. There is one finite list of commands $I_i := \pi_{R_i}(I_i\bowtie I_j)$ that makes **every** instance globally consistent.
   A command reads the current relations, changes only $I_i$, and preserves $J$; hence the final extents are precisely the projections of the original $J$.
3. There is a tree on the relation schemes such that each attribute shared by two schemes occurs in every scheme on their unique path.
   Equivalently, label a tree edge by the intersection of its endpoints: every edge on the path carries the shared attribute.
4. Every maximal GYO ear-removal run ends with no edges. In the current family an edge $f$ is an ear if it meets no other edge,
   or if a single other edge contains every attribute that $f$ shares with any other edge. Remove $f$ and take the union of the surviving edges as the new vertex set.
   The last edge is isolated and can be removed. Each step removes one edge, so a maximal run terminates.

The nonempty *schemes* follow the hyperedge convention of §6.4 (p. 130); the named relational model of §3.2 also admits nullary relations.
No connectivity or nonempty-*extent* hypothesis is needed. Disjoint schemes may be neighbours with an empty tree-edge label.
An empty extent makes the full join empty; global consistency then requires every extent to be empty.

These are the first four properties of the source theorem. Its fifth property characterizes the same schemas by articulation sets:
reduce the hypergraph by discarding properly contained edges; every connected restriction with more than one edge must have an articulation set.
Restriction here intersects the edges with the chosen vertex set, discards empty intersections and reduces again.
An articulation set is an intersection of two distinct edges whose deletion increases the number of connected components.

## Sources

- S. Abiteboul, R. Hull and V. Vianu, [*Foundations of Databases*](https://webdam.di.ens.fr/Alice/pdfs/all.pdf), Addison-Wesley, 1995, §6.4: properties (1)–(3), pp. 128–129; ears, Algorithm 6.4.4 and property (4), p. 131; property (5) and Theorem 6.4.5, p. 132 (PDF p. 134); proof sketch, pp. 132–134, and Exercises 6.28 and 6.30, p. 141.
