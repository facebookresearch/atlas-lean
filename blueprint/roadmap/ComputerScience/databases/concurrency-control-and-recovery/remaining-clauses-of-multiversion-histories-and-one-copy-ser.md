# Multiversion histories and one-copy serializability

This node extends the model of multiversion histories, in which a version function assigns to each read the write
whose version it returns (or the initial version), with the following definitions.

## Expansion

A sound expansion has separate pages for:

1. **Commit and abort,** and for snapshot isolation start and commit times, in multiversion histories.
2. **Monoversion image:** replacing each version by its item.
3. **One-copy serializability (1SR):** a multiversion history is 1SR if its committed projection is
   equivalent, that is, has the same operations and the same reads-from relation on versions, to a one-copy
   serial history: a serial multiversion history in which each transaction reads every item from itself or
   from the last preceding transaction that writes it. Equivalently, the committed projection has the same
   reads-from relation as some serial single-version history; final writes are not compared, since no
   version is overwritten. 1SR is not view serializability of the monoversion image, which can differ when
   reads see older versions.
4. **Embedding:** a single-version history embeds as the multiversion history whose version function picks
   the latest preceding write. If the single-version history is view serializable, its embedding is 1SR. The
   converse fails because one-copy equivalence ignores final writes: $r_1[x]\,w_2[x]\,w_1[x]\,c_1\,c_2$ embeds
   as a 1SR history, equivalent to running $T_1$ before $T_2$, but is not view serializable. Requiring in
   addition that each item's last version in the history be written by the transaction that writes it last
   in the serial history makes the two notions coincide on embedded histories.

## Sources

- P. A. Bernstein, V. Hadzilacos and N. Goodman, *Concurrency Control and Recovery in Database Systems*, Addison-Wesley, 1987 (authors' free edition), Section 5.2: multiversion histories and translation functions (p. 147), equivalence by reads-from with final writes dropped and Proposition 5.1 (p. 148), one-copy serial and 1SR histories and Theorem 5.3 (p. 150). <https://www.microsoft.com/en-us/research/wp-content/uploads/2016/05/chapter5.pdf>
- A. Fekete, D. Liarokapis, E. O'Neil, P. O'Neil and D. Shasha, *Making snapshot isolation serializable*, ACM TODS 30(2), 2005, Section 1.1 (versioned histories, pp. 494–495). <https://cs.nyu.edu/~shasha/papers/serializablesnap>
- A Critique of ANSI SQL Isolation Levels (Berenson, Bernstein, Gray, Melton, O'Neil, O'Neil), SIGMOD 1995, Section 4.2 (snapshot isolation with start and commit timestamps). <https://courses.cs.duke.edu/compsci516/cps216/spring03/papers/berenson-etal-1995.pdf>
