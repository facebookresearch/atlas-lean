# Counting the initial clauses

There are at most $\sum_{j=0}^{k} (2t)^j$ clauses of at most $k$ literals over $t$ variables: there
are $2t$ literals, hence at most $\binom{2t}{j} \le (2t)^j$ clauses of exactly $j$ literals. Valiant
counts the clauses of one to $k$ literals as fewer than $(2t)^{k+1}$; the sum here also counts the
empty clause.

## Sources

- L. G. Valiant, *A theory of the learnable*, Communications of the ACM 27 (1984), 1134-1142, Section 5, proof of Theorem A.
