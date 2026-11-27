# Boolean clones

A *(positive-arity) Boolean clone* is a set $C$ of operations $f : \{0,1\}^n \to \{0,1\}$ with $n \ge 1$ that contains every projection $(x_1,\dots,x_n) \mapsto x_i$ and is closed under superposition: if $f \in C$ has arity $m$ and $g_1,\dots,g_m \in C$ all have arity $n$, then $(x_1,\dots,x_n) \mapsto f(g_1(x),\dots,g_m(x))$ lies in $C$. Clones are closed under taking *minors* (permuting, identifying and adding dummy variables). The clone *generated* by a family $G$ of operations is the least clone containing $G$; it consists of the operations obtained from members of $G$ and projections by finitely many superpositions. A family is *complete* if it generates every positive-arity Boolean operation. Ordered by inclusion, the Boolean clones form Post's lattice.

## Sources

- E. L. Post, The Two-Valued Iterative Systems of Mathematical Logic, Annals of Mathematics Studies 5, Princeton University Press, 1941.
- F. J. Pelletier and N. M. Martin, "Post's Functional Completeness Theorem", Notre Dame Journal of Formal Logic 31(3), 462–475, 1990.
- H. Chen, "A Rendezvous of Logic, Complexity, and Algebra", SIGACT News 37(4), 85–114, 2006 (extended version ACM Computing Surveys 42(1), 2009).
