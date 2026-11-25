# A ready check followed by an optional read never delivers an empty sample

Extend the [overwrite-newest sampled register](overwrite-register-reads-return-increasing-publications.md) with an event
$\mathsf{Ready}$ that reports whether the state is nonempty and changes nothing. A driver performs $\mathsf{Ready}$ and, if it
reports nonempty, performs one $\mathsf{Read}$, delivering $(n, v)$ as a sample when the read returns a pair and delivering
nothing when it returns $\bot$. Let any number of $\mathsf{Publish}$ events and $\mathsf{Read}$ events of other readers interleave
between the driver's $\mathsf{Ready}$ and its $\mathsf{Read}$. Then in every such interleaving the driver never delivers $\bot$
as a sample, and every sample $(n, v)$ it delivers is the $n$-th publication, with its actual value.

A $\mathsf{Ready}$ that reports nonempty does not ensure that the following read succeeds, since another reader may empty the slot
in between; the driver then delivers nothing rather than a stale value. Correctness here rests on the atomic optional read, which returns the slot and empties it in one step.

## Depends on

- [Reads of an overwrite-newest register return increasing publications](overwrite-register-reads-return-increasing-publications.md)

## Sources

- H. Kopetz, *Real-Time Systems: Design Principles for Distributed Embedded Applications*, 2nd edition, Springer, 2011, Chapter 4 (state messages with update-in-place semantics).
- N. A. Lynch, *Distributed Algorithms*, Morgan Kaufmann, 1996, Chapter 8 (automata, traces and simulation relations).
