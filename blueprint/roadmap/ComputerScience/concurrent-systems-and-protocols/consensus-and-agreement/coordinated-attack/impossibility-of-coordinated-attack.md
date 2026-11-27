# Impossibility of coordinated attack

Consider a synchronous system with unreliable links. Its processes form a set $G$ with at least two elements, not necessarily finite, and each process starts with an input from a set $V$ of at least two values; in the source there are $n \ge 2$ processes and the inputs are $0$ (retreat) and $1$ (attack). In each round $r = 0, 1, \ldots$, every process may send one message to every process, itself included, receives those messages of round $r$ to it that are delivered, and updates its state. Any message may be lost: the messages delivered in a round can be any subset, possibly empty, of those sent in it, and a receiver cannot tell a lost message from one that was never sent.

A deterministic protocol gives each process its initial state as a function of its input, the message it sends to each process in round $r$ (or none) as a function of $r$ and its state, its state after round $r$ as a function of $r$, its state and the messages it received in round $r$, and its decision, a value in $V$, as a function of its state after a fixed number $T$ of rounds. So termination within a bounded number of rounds is built in; a process that decides earlier can keep its decision in its state. The protocol solves the coordinated attack problem in $T$ rounds if:

- **Agreement:** for all inputs and every pattern of lost messages, all processes decide the same value;
- **Validity:** if all processes have the same input $x$ and no message is lost, all processes decide $x$.

For every $T$, no deterministic protocol solves the coordinated attack problem in $T$ rounds.

**Proof.** The proof is by indistinguishability. If two executions are indistinguishable to some process, then by agreement every process decides the same value in both. Fix two values $a \ne b$ in $V$ and two processes $p \ne q$.

- Start from the execution with all inputs $a$ and no message lost, in which all processes decide $a$. Delete the messages of the last round, then those of the round before, and so on, each round in two batches: first its messages to every process other than $p$, then its messages to $p$. A deletion changes only what the receivers of the deleted messages see, and since no later message is delivered, they cannot pass the change on. So the first batch leaves the execution indistinguishable to $p$, and the second leaves it indistinguishable to $q$.
- Once no messages are delivered at all, change the inputs from $a$ to $b$, first for every process other than $p$, then for $p$. With no messages delivered, each change is invisible to $p$ and to $q$ respectively.
- Finally add back the messages in the same way, reaching the execution with all inputs $b$ and no message lost, in which all processes decide $b$.

This chain of executions forces the same decision at both ends, a contradiction. The source deletes and adds back one message at a time, which needs finitely many processes; the two batches per round do not.

With two processes this is Gray's Two Generals problem.

## Sources

- J. Aspnes, *Notes on Theory of Distributed Systems*, Yale University, <https://cs.yale.edu/homes/aspnes/classes/4650/notes.pdf> (also arXiv:2001.04235), Chapter 8: Section 8.1 (formal description, agreement, validity and termination) and Section 8.2 (the impossibility proof by a chain of indistinguishable executions).
- N. A. Lynch, *Distributed Algorithms*, Morgan Kaufmann, 1996, Section 5.1.
- J. N. Gray, "Notes on data base operating systems", in *Operating Systems: An Advanced Course*, Lecture Notes in Computer Science, Springer, 1978, pp. 393–481.
