# The target's clauses are never deleted

If $f$ is a $k$-CNF expression and every example satisfies $f$, then every clause of $f$ survives
elimination. This is the special case, for the clauses of $f$ itself, of Valiant's observation that
"in the course of the algorithm no clause in $B$ can ever be deleted", where $B$ is the set of all
clauses of at most $k$ literals implied by $f$.

## Sources

- L. G. Valiant, *A theory of the learnable*, Communications of the ACM 27 (1984), 1134-1142, Section 5, proof of Theorem A.
