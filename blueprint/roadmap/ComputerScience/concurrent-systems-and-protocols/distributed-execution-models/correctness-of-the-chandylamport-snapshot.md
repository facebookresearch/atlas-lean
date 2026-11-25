# Correctness of the Chandy–Lamport snapshot algorithm

Consider a distributed system of processes connected by channels that are reliable and FIFO, in which the processes and channels form a strongly connected graph. In the Chandy–Lamport algorithm, a process that initiates the snapshot, or receives its first marker, records its own state and then sends a marker on every outgoing channel before sending any other message on it. The state recorded for an incoming channel $c$ is the sequence of messages received on $c$ after the process recorded its own state and before it received the marker on $c$. This sequence is empty if the marker on $c$ triggered the recording. The algorithm terminates once every process has received a marker on every incoming channel.

Let $\mathit{seq} = (e_i)_{i \ge 0}$ be the computation, and $S_i$ the global state immediately before $e_i$. Let the algorithm be initiated in state $S_\iota$ and terminate in state $S_\phi$, and let $S^*$ be the recorded global state. $S^*$ need not be any of the states $S_\iota, \dots, S_\phi$, but:

**Theorem.** There is a computation $\mathit{seq}'$ that agrees with $\mathit{seq}$ before $e_\iota$ and from $e_\phi$ on, permutes the events $e_\iota, \dots, e_{\phi - 1}$, has the same global states as $\mathit{seq}$ up to $S_\iota$ and from $S_\phi$ on, and passes through $S^*$. Hence $S^*$ is reachable from $S_\iota$, and $S_\phi$ is reachable from $S^*$.

The permutation moves every event that occurs at a process before that process records its state ahead of every event that occurs after recording. By the FIFO property no message sent after its sender's recording is received before its receiver's recording, so the reordered sequence is again a computation. Consequently a stable property, one that remains true once it holds, that holds in $S^*$ also holds in $S_\phi$. If it does not hold in $S^*$, it did not hold in $S_\iota$.

## Depends on

- [Consistent cuts and their lattice](consistent-cuts-and-their-lattice.md)

## Proof depends on

- [Consistency of the Chandy–Lamport snapshot](../snapshot-consistent.md)

## Sources

- K. M. Chandy and L. Lamport, "Distributed snapshots: determining global states of distributed systems", *ACM Transactions on Computer Systems* 3(1):63–75, 1985, <https://lamport.azurewebsites.net/pubs/chandy.pdf>: Section 3 (the algorithm and its marker rules), Section 4 (Theorem 1 and its proof by prerecording and postrecording events), and the application to stable property detection.
- J. Aspnes, *Notes on Theory of Distributed Systems*, Yale University, <https://cs.yale.edu/homes/aspnes/classes/4650/notes.pdf>, Section 6.3 (consistent snapshots and the Chandy–Lamport algorithm).
