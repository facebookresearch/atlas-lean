# Timestamp ordering and multiversion concurrency control

This node collects timestamp-ordering protocols and their serializability guarantees.

## Expansion

A sound expansion has separate pages for:

1. **Basic timestamp ordering.** Each transaction gets a unique timestamp at start; each item keeps its
   largest read and write timestamps; a read by $T$ is rejected (and $T$ restarts with a new timestamp) if a
   younger transaction has written the item, and a write is rejected if a younger transaction has read or
   written it. The committed transactions of every history produced, each with the timestamp of its successful
   run, form a schedule conflict-equivalent to the serial schedule in timestamp order; the history need not be
   recoverable.
2. **Multiversion timestamp ordering.** Each write creates a version tagged with the writer's timestamp (a
   second write of the same item by $T$ overwrites $T$'s version); a read by $T$ returns the version with the
   largest timestamp not exceeding $T$'s; a write by $T$ is rejected if some transaction with a larger timestamp
   has already read the version that $T$'s write would supersede. With commit dependencies tracked (no commit
   before the writers of the versions read commit), the committed transactions of every history produced form a
   one-copy serializable history, equivalent to the serial history in timestamp order.

## Depends on

- [Conflict equivalence](../conflict-serializability/conflict-equiv.md)
- [Serial schedule](../conflict-serializability/is-serial.md)
- [Multiversion histories and one-copy serializability](remaining-clauses-of-multiversion-histories-and-one-copy-ser.md)

## Proof depends on

- [The serializability theorem](../conflict-serializability/conflict-serializable-iff-is-acyclic.md)

## Sources

- P. A. Bernstein, V. Hadzilacos and N. Goodman, *Concurrency Control and Recovery in Database Systems*, Addison-Wesley, 1987 (authors' free edition), Theorem 4.1 (TO histories are serializable, p. 114) and the remark that the TO rule does not ensure recoverability (p. 116); Theorem 5.5 (every MVTO history is one-copy serializable, p. 155). <https://www.microsoft.com/en-us/research/wp-content/uploads/2016/05/chapter4.pdf> <https://www.microsoft.com/en-us/research/wp-content/uploads/2016/05/chapter5.pdf>
- A. Silberschatz, H. F. Korth and S. Sudarshan, *Database System Concepts*, 7th edition, Chapter 18 slides 18.40–18.42 (timestamp-ordering rules), 18.45 (all precedence-graph edges go from smaller to larger timestamps), 18.46 (recoverability needs commit dependencies) and 18.55–18.57 (multiversion timestamp ordering and its serializability). <https://www.db-book.com/slides-dir/PDF-dir/ch18.pdf>
