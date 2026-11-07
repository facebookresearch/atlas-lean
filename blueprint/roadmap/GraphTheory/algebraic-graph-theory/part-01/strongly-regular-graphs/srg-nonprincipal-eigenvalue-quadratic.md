# Non-principal eigenvalues of a connected non-complete strongly regular graph

Let $G$ be a
finite strongly regular graph with parameters $(n, k, \ell, \mu)$: $G$ has $n$ vertices, every
vertex has degree $k$, any two adjacent vertices have exactly $\ell$ common neighbors, and any
two distinct nonadjacent vertices have exactly $\mu$ common neighbors. Suppose that $G$ is
connected and not complete, and let $A$ be its adjacency matrix over $\mathbb{C}$. Then every
eigenvalue $x \in \mathbb{C}$ of $A$ with $x \neq k$ satisfies $x^2 = (\ell - \mu) x + (k - \mu)$.

Proof: Apply the identity $A^2 = kI + \ell A + \mu \bar{A}$, where $I$ is the identity matrix
and $\bar{A}$ is the adjacency matrix of the complement of $G$, to an eigenvector $v$ for $x$;
regularity makes the coordinate sum of $v$ zero, so $\bar{A} v = -(1 + x) v$, and this gives
the quadratic. This is the proof of Theorem 9.1.2, (ii) ⇒ (iii), in Brouwer and Haemers,
Section 9.1.3.

## Sources

- A. E. Brouwer and W. H. Haemers, Spectra of Graphs, Springer 2012, Ch. 9, eigenvalues of strongly regular graphs; C. Godsil and G. Royle, Algebraic Graph Theory, GTM 207, Ch. 10 (eigenvalues of strongly regular graphs).
