# The asynchronous shared-memory model

In an asynchronous shared-memory system, $n$ processes communicate through shared base objects,
such as atomic registers or read-modify-write objects. A running process is a state machine:
its local state determines both its next operation on a particular object and how it will
update its state on receiving the operation's reply. Each object has its own state and atomic
operations, each of which takes the state of that object and returns a reply and a new state.
The initial state of every process and object is specified.
A process with no next operation is halted as soon as it enters that local state,
including at initialization. Normal halting needs no additional scheduled event.
Halting preserves the final local state, including any reply the process has stored.

The [configuration](configuration.md) collects all these states. A schedule picks one
event at a time; the [transition rule](step.md) updates only the participating process
and, for an atomic operation, its selected object. These transitions give
[finite](finite-execution.md) and [infinite](infinite-execution.md) executions and
a [fairness condition](fair.md) for infinite executions with halts or
crash-stop failures.

## Sources

- J. Aspnes, *Notes on Theory of Distributed Systems*, Yale University, 2020, <https://arxiv.org/abs/2001.04235>, the chapter "Model" of Part II (shared memory), sections on atomic registers and on fairness and crashes
- M. Herlihy, "Wait-free synchronization", *ACM Transactions on Programming Languages and Systems* 13(1):124–149, 1991
