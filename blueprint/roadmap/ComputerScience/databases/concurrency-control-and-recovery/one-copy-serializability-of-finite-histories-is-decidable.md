# One-copy serializability of finite histories is decidable

For a finite multiversion history $H$, it is decidable whether $H$ is one-copy serializable: $H$ is one-copy serializable if and only if for some
ordering of the committed transactions of $H$, the one-copy serial history in that order has the same reads-from relation on versions as the committed
projection of $H$, and there are finitely many orderings to check.

## Proof

One-copy serializability of $H$ is, by definition, equivalence of its committed projection to a one-copy serial history over the same transactions;
that equivalence is equality of the reads-from relations, which is computable for finite histories, and a one-copy serial history is determined by its
order of transactions.

## Depends on

- [Multiversion histories and one-copy serializability](remaining-clauses-of-multiversion-histories-and-one-copy-ser.md)

## Sources

- P. A. Bernstein, V. Hadzilacos and N. Goodman, *Concurrency Control and Recovery in Database Systems*, Addison-Wesley, 1987 (authors' free edition), Section 5.2: equivalence of multiversion histories and Proposition 5.1 (p. 148), one-copy serial and one-copy serializable histories and Theorem 5.3 (p. 150). <https://www.microsoft.com/en-us/research/wp-content/uploads/2016/05/chapter5.pdf>
