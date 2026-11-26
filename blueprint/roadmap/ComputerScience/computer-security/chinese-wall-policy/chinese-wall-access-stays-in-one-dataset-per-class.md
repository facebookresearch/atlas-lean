# After an access, a request is granted only within the dataset or across classes

**Theorem 1.** In the [Chinese Wall model](chinese-wall-model.md), once a subject has accessed an object, the only other objects accessible by that subject lie
within the same company dataset or within a different conflict of interest class. Prospectively: if a subject $s_u$ has accessed $o_a$ (that is, $N(u, a)$ is true in
the current matrix $N$, reached from the initial state of Axiom 3 by granting requests according to Axioms 2 and 4), then a request $R(u, b)$ for an object $o_b$ can
be granted only if $x_a \ne x_b$ or $y_a = y_b$.

This is immediate from Axiom 2 applied to the request $R(u, b)$ and the earlier access to $o_a$.

## Depends on

- [The Chinese Wall model](chinese-wall-model.md)

## Sources

- D. F. C. Brewer and M. J. Nash, "The Chinese Wall security policy", *Proceedings of the 1989 IEEE Symposium on Security and Privacy*, pp. 206–214, copy at <https://cgi.cse.unsw.edu.au/~meyden/3441/brewernash.pdf>: Annex A, Theorem 1 and its proof, p. 212.
