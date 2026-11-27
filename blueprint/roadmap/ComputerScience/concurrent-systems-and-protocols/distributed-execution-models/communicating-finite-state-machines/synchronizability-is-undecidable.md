# Synchronizability of communicating finite-state machines is undecidable

It is undecidable whether a system of communicating finite-state machines with peer-to-peer FIFO channels is synchronizable, and also whether it is language synchronizable; the reduction produces systems of three peers.

**Theorem.** The following problems are undecidable. Input: a message set and a system $\mathcal{S}$ of communicating finite-state machines with peer-to-peer FIFO channels. Questions: is $\mathcal{S}$ [synchronizable](synchronizability-of-communicating-machines.md) ($\mathit{sTr}_0(\mathcal{S}) = \mathit{sTr}(\mathcal{S})$)? Is $\mathcal{S}$ language synchronizable ($\mathit{sTr}^{w}_0(\mathcal{S}) = \mathit{sTr}^{w}(\mathcal{S})$)? The source establishes both for systems of three peers.

## Depends on

- [Synchronizability of communicating machines](synchronizability-of-communicating-machines.md)

## Proof depends on

None.

## Expansion

The proof reduces the message reception problem for FIFO automata, finite automata that enqueue and dequeue on a single FIFO queue: given such an automaton $\mathcal{A}$ and a message $m$, is there a trace $\tau$ with $\tau \cdot ?m$ a trace of $\mathcal{A}$? This problem is undecidable (Lemma 3.3 of the source, proved from the undecidability of tiling problems in the style of Lewis and Papadimitriou). A FIFO automaton is simulated by a system of three peers whose communication is constrained enough that the system is (language) synchronizable iff $m$ is never received in $\mathcal{A}$. Three peers are needed by this proof: synchronizability forces commutations of sends and receives that prevent a synchronizable two-peer system from simulating a FIFO automaton, and synchronizability of two-peer systems is decidable. For oriented rings, synchronizability coincides with $1$-synchronizability and is decidable (Section 4).

## Sources

- Alain Finkel and Etienne Lozes, "Synchronizability of communicating finite state machines is not decidable", *Logical Methods in Computer Science* 19(4), article 33, 2023, <https://doi.org/10.46298/lmcs-19(4:33)2023>; read as arXiv:1702.07213v7, <https://arxiv.org/abs/1702.07213v7>, the journal version: Theorem 3.14 and its proof, Definition 3.1 and Lemma 3.3 (message reception), and the summary of contributions in Section 1.
