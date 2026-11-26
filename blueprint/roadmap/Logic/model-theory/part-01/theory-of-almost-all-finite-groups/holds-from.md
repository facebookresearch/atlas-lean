# Truth of a quantifier prefix followed by a matrix

Let $G$ be a group and $m$ a CNF matrix of group literals. For $d \in \mathbb{N}$, a list of quantifier flags $q$ and an assignment $x : \mathbb{N} \to G$, the truth value $H(d, q, x)$ of the prefix $q$, whose first quantifier binds $x_d$, followed by $m$, is defined by recursion on $q$:

- $H(d, [\,], x)$ holds iff the matrix $m$ holds under $x$;
- $H(d, \mathrm{true} :: q, x)$ holds iff $H(d + 1, q, x[d \mapsto g])$ holds for every $g \in G$;
- $H(d, \mathrm{false} :: q, x)$ holds iff $H(d + 1, q, x[d \mapsto g])$ holds for some $g \in G$.

Here $x[d \mapsto g]$ is the assignment that agrees with $x$ except that it sends $d$ to $g$.
