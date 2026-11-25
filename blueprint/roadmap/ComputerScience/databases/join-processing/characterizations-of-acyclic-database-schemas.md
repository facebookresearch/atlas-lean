# Characterizations of acyclic database schemas

Let $\mathbf{R} = \{R_1, \dots, R_n\}$ be a database schema of distinct relation schemas, viewed as a hypergraph whose
vertices are the attributes and whose hyperedges are the relation schemas. An instance $I$ over $\mathbf{R}$ is
*pairwise consistent* if $\pi_{R_j}(I_j \bowtie I_k) = I_j$ for all $j, k$, and *globally consistent* if
$\pi_{R_j}(I_1 \bowtie \cdots \bowtie I_n) = I_j$ for all $j$. A *full reducer* is a program of semijoins that maps every
instance to a globally consistent instance. A *join tree* is a tree whose nodes are the relation schemas such that
for any two nodes $R, R'$ and every attribute $A \in R \cap R'$, every node on the path between $R$ and $R'$ contains
$A$. An *ear* is a hyperedge $f$ such that, for some other hyperedge $f'$, every attribute of $f$ that occurs in
another hyperedge occurs in $f'$ (a hyperedge meeting no other hyperedge is also an ear); the GYO algorithm
repeatedly removes ears.

The following are equivalent:

1. every pairwise consistent instance over $\mathbf{R}$ is globally consistent;
2. $\mathbf{R}$ has a full reducer;
3. $\mathbf{R}$ has a join tree;
4. the GYO algorithm reduces $\mathbf{R}$ to the empty hypergraph.

Schemas with these properties are called acyclic.

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995 (authors' web edition), Theorem 6.4.5. <http://webdam.inria.fr/Alice/pdfs/all.pdf>
