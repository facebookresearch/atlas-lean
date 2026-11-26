# Blocking of atomic commitment protocols

A process running an atomic commitment protocol (see [Atomic commitment and blocking of two-phase commit](atomic-commitment-and-blocking-of-two-phase.md) for the specification AC-1 to AC-5) is *blocked* when its progress depends on the repair of failures. A process that fails and, during recovery, reaches a decision without communicating with other processes *recovers independently*. A *total failure* is a failure of all processes.

**Proposition 1.** If communication failures or total failures are possible, then every atomic commitment protocol may cause processes to become blocked.

**Proposition 2.** No atomic commitment protocol can guarantee independent recovery of failed processes.

## Expansion

The source states both propositions without a model or a proof. A good expansion adds a model of atomic commitment protocols in which processes exchange messages, crash, recover from stable storage and lose messages, defines blocking and independent recovery in it, adds a page defining the specification AC-1 to AC-5 for such protocols, and states each proposition on a page of its own.

## Sources

- L. Alvisi, *Atomic Commit*, lecture notes, CS 371D Distributed Computing, University of Texas at Austin, Fall 2008, <https://www.cs.utexas.edu/~lorenzo/corsi/cs371d/08F/notes/week3.pdf>: the definitions of blocking, independent recovery and total failure, Proposition 1 and Proposition 2 ("A few character-building facts"), and the remark that no atomic commitment protocol is non-blocking in the presence of communication or total failures.
