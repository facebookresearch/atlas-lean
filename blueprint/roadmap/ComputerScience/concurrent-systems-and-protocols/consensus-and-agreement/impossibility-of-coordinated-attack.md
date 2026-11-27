# Impossibility of coordinated attack

Consider $n \ge 2$ processes in a synchronous system with unreliable channels. The set of messages received in round $i + 1$ is always a subset, possibly a proper subset and possibly empty, of the set sent in round $i$. Each process starts with input $0$ or $1$. The coordinated attack problem requires, in every execution:

- **Agreement:** all processes output the same decision;
- **Validity:** if all processes have the same input $x$ and no message is lost, all processes output $x$;
- **Termination:** all processes decide within a bounded number of rounds.

No deterministic protocol satisfies all three conditions.

**Proof.** The proof is by indistinguishability. If two executions are indistinguishable to some process, then by agreement every process outputs the same value in both.
- Start from the execution with all inputs $1$ and no message lost, in which all processes output $1$. Delete the messages of the last round one at a time, then those of the round before, and so on. Each deletion changes only what the receiver of that message sees, so consecutive executions are indistinguishable to some other process.
- Once no messages are delivered at all, change the inputs from $1$ to $0$ one process at a time. With no messages delivered, each change is invisible to every other process.
- Finally add back the messages one at a time, reaching the execution with all inputs $0$ and no message lost, in which all processes must output $0$.

This chain of executions forces the same output at both ends, a contradiction.

With two processes this is Gray's Two Generals problem. Because each round has finitely many possible outcomes, requiring termination in finitely many rounds is equivalent to requiring a bounded number of rounds, by König's lemma.

## Sources

- J. Aspnes, *Notes on Theory of Distributed Systems*, Yale University, <https://cs.yale.edu/homes/aspnes/classes/4650/notes.pdf> (also arXiv:2001.04235), Chapter 8: Section 8.1 (formal description, agreement, validity and termination, with the footnote on bounded and finite termination) and Section 8.2 (the impossibility proof by a chain of indistinguishable executions).
- N. A. Lynch, *Distributed Algorithms*, Morgan Kaufmann, 1996, Section 5.1.
- J. N. Gray, "Notes on data base operating systems", in *Operating Systems: An Advanced Course*, LNCS 60, Springer, 1978.
