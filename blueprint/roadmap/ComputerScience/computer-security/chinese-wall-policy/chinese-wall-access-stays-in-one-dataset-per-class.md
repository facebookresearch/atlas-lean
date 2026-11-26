# Chinese Wall access stays within a dataset or across classes

**Theorem 1.** In the [Chinese Wall model](chinese-wall-model.md), once a subject has accessed an object, the only other objects accessible by that subject lie
within the same company dataset or within a different conflict of interest class: in every access matrix $N$ reached from the initial state of Axiom 3 by
granting requests according to Axioms 2 and 4, if $N(u, a)$ and $N(u, b)$ are both true, then $x_a \ne x_b$ or $y_a = y_b$.

If access to $o_a$ was granted first, the later grant of $o_b$ required $x_a \ne x_b$ or $y_a = y_b$ by Axiom 2.

## Depends on

- [The Chinese Wall model](chinese-wall-model.md)

## Sources

- D. F. C. Brewer and M. J. Nash, "The Chinese Wall security policy", *Proceedings of the 1989 IEEE Symposium on Security and Privacy*, pp. 206–214, copy at <https://cgi.cse.unsw.edu.au/~meyden/3441/brewernash.pdf>: Annex A, Theorem 1 and its proof, p. 212.
