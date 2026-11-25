# Recoverable, cascadeless and strict schedules

This node collects recoverability classes of transaction histories with commit and abort.

## Expansion

A sound expansion has separate pages for:

1. **Histories.** Finite histories of read, write, commit and abort operations in which every transaction has at
   most one commit or abort and no operation after it. $T_j$ reads $x$ from $T_i$ ($i \ne j$) when $T_j$ reads $x$
   after $T_i$ wrote it, $T_i$ has not aborted before the read, and every transaction that wrote $x$ in between
   has aborted before the read.
2. **Classes.** Recoverable (RC): whenever $T_j$ reads from $T_i$ and $T_j$ commits, $T_i$ commits before $T_j$
   does. Avoids cascading aborts (ACA): whenever $T_j$ reads $x$ from $T_i$, $T_i$ has committed before that read.
   Strict (ST): whenever $T_i$ writes $x$ before an operation of another transaction that reads or writes $x$,
   $T_i$ has committed or aborted before that operation.
3. **Inclusions.** ST $\subsetneq$ ACA $\subsetneq$ RC, with witnesses: $w_1[x]\,w_2[x]\,c_1\,c_2$ is ACA but not ST,
   and $w_1[x]\,r_2[x]\,c_1\,c_2$ is RC but not ACA. Conflict serializability is incomparable with RC:
   $w_1[x]\,r_2[x]\,c_2\,c_1$ is conflict-serializable but not RC, and $w_1[x]\,w_2[x]\,w_2[y]\,c_2\,w_1[y]\,c_1$ is
   RC but not conflict-serializable.
4. **Strict two-phase locking,** with every lock held until its transaction commits or aborts, produces strict,
   conflict-serializable histories. Conflict serializability follows from the strict two-phase locking theorem for
   schedules without commit and abort; strictness needs commit and abort in the lock model.

## Depends on

- [Operation of a schedule](../conflict-serializability/op.md)
- [Strict two-phase schedules](../two-phase-locking/strict-two-phase.md)

## Proof depends on

- [Strict two-phase locking theorem](../two-phase-locking/conflict-serializable-2.md)

## Sources

- P. A. Bernstein, V. Hadzilacos and N. Goodman, *Concurrency Control and Recovery in Database Systems*, Addison-Wesley, 1987 (authors' free edition), Section 2.4: reads-from, RC, ACA and ST (pp. 34–35), Theorem 2.2 (ST ⊂ ACA ⊂ RC, proper) and the incomparability of SR with each class (p. 35); Section 3 (Strict 2PL produces strict executions, pp. 59–60). <https://www.microsoft.com/en-us/research/wp-content/uploads/2016/05/chapter2.pdf> <https://www.microsoft.com/en-us/research/wp-content/uploads/2016/05/chapter3.pdf>
- A. Silberschatz, H. F. Korth and S. Sudarshan, *Database System Concepts*, 7th edition, Chapter 17 slides 17.28–17.30 (recoverable and cascadeless schedules; every cascadeless schedule is recoverable). <https://www.db-book.com/slides-dir/PDF-dir/ch17.pdf>
- A. Silberschatz, H. F. Korth and S. Sudarshan, *Database System Concepts*, 7th edition, Chapter 18 slide 18.10 (strict two-phase locking ensures recoverability and avoids cascading roll-backs). <https://www.db-book.com/slides-dir/PDF-dir/ch18.pdf>
