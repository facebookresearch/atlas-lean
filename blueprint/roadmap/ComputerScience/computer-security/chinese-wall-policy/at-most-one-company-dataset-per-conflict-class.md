# At most one company dataset per conflict class

**Theorem 2.** In the [Chinese Wall model](chinese-wall-model.md), a subject can at most have access to one company dataset in each conflict of interest class: in
every access matrix $N$ reachable from the initial state of Axiom 3 by granting requests according to Axioms 2 and 4, if $N(u, a)$ and $N(u, b)$ are true and
$x_a = x_b$, then $y_a = y_b$.

A subject needs no access initially (Axiom 3); its first request succeeds (Axiom 4), and by induction on the
granted requests, [Theorem 1](chinese-wall-access-stays-in-one-dataset-per-class.md) lets each later grant in a class only within the dataset of the first access there.

## Depends on

- [The Chinese Wall model](chinese-wall-model.md)

## Proof depends on

- [After an access, a request is granted only within the dataset or across classes](chinese-wall-access-stays-in-one-dataset-per-class.md)

## Sources

- D. F. C. Brewer and M. J. Nash, "The Chinese Wall security policy", *Proceedings of the 1989 IEEE Symposium on Security and Privacy*, pp. 206–214, copy at <https://cgi.cse.unsw.edu.au/~meyden/3441/brewernash.pdf>: Annex A, Theorem 2 and its proof, p. 212.
