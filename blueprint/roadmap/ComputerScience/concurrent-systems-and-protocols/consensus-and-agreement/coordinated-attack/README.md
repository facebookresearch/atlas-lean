# Impossibility of coordinated attack

Consider a synchronous system whose links may lose any message, with a set of processes that has at least two elements, not necessarily finite, and inputs and decisions in a set of at least two values. In each round every process may send one message to every process, itself included, and any of them may be lost; a receiver cannot tell a lost message from one that was never sent. Every deterministic protocol in which each process decides from its state after a fixed number $T$ of rounds fails agreement (in some execution two processes decide differently) or validity (in some execution where all inputs are $x$ and no message is lost, some process does not decide $x$).

## Idea

Two generals who can only communicate by messengers that may be captured can never be sure of attacking together. If a message of the last round is lost, only its receiver notices, and it has no later message to pass the news on; by agreement, the receiver decides as everyone else does, and everyone else decides as before. Deleting the messages of each round, from the last back to the first, in two batches (first those to every process but one, then those to that one), then changing the inputs in two batches in the same way, links the execution in which all inputs are $a$ and nothing is lost, where validity forces the decision $a$, to the one in which all inputs are $b$, where it forces $b$: no protocol can decide both ways.

## Statements

- [Impossibility of coordinated attack](impossibility-of-coordinated-attack.md)
- [Synchronous protocol over lossy links](lossy-protocol.md): the protocols
- [Execution with message loss](state-after.md): their executions under a pattern of lost messages
- [Solving coordinated attack in `T` rounds](solves-coordinated-attack.md): agreement and validity

## Sources

- J. Aspnes, *Notes on Theory of Distributed Systems*, Yale University, <https://cs.yale.edu/homes/aspnes/classes/4650/notes.pdf> (also arXiv:2001.04235), Chapter 8: Sections 8.1 and 8.2.
- N. A. Lynch, *Distributed Algorithms*, Morgan Kaufmann, 1996, Section 5.1.
