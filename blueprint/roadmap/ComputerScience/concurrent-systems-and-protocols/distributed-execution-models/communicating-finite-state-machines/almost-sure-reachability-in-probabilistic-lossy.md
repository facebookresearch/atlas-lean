# Almost-sure reachability in probabilistic lossy channel systems is undecidable

For probabilistic lossy channel systems in which each sent message is lost with a fixed probability at the moment it is sent, it is undecidable whether a given control state is reached with probability one, so safety and liveness properties cannot be checked almost surely.

**Probabilistic lossy channel systems.** A *probabilistic lossy channel system* (PLCS) is a tuple $\langle S, C, M, \delta, W, \lambda \rangle$ where $\langle S, C, M, \delta \rangle$ is a system of finite-state processes with send, receive and empty transitions over unbounded FIFO channels $C$ (a [lossy channel system](lossy-channel-systems.md) in which, in this model, a message can be lost only when it is sent), $\lambda \in [0,1]$ is the probability of losing a message and $W$ assigns a positive weight to each transition; as inputs, $\lambda$ and the weights are rational numbers. Every control state is required to have at least one outgoing send or empty transition: such a transition is always enabled, so at every global state the weights of the enabled transitions have a positive sum (the source notes, after Definition 4, that the step probabilities are well defined only under this condition, and its construction satisfies it). At a global state, the enabled transitions are chosen with probability proportional to their weights; a chosen send succeeds with probability $1 - \lambda$ and loses its message with probability $\lambda$; once a message is in a channel it leaves only by being received. Runs from the initial global state (control state $s_{\mathit{init}}$, all channels empty) carry the usual probability measure on cylinder sets.

**Problem.** Reach-PLCS: given a PLCS $L$ and a control state $s_F$, is the probability that a run of $L$ from the initial global state reaches a global state with control state $s_F$ equal to $1$?

**Theorem (Abdulla, Baier, Iyer and Jonsson).** Reach-PLCS is undecidable (Theorem 18).

The loss probability $\lambda$ and the weights are part of the input; as finite data they are rational numbers. The source defines them as a real number in $[0,1]$ and positive reals, and its construction gives every transition the same weight (Section 6, which notes that any positive weights would do), so undecidability already holds with all weights equal to $1$. By contrast, in the model of Baier and Engelen, where the next step is a loss with a fixed probability and losses can occur at any time, checking properties with probability one is decidable when the loss probability is high enough.

## Depends on

- [Lossy channel systems](lossy-channel-systems.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The reduction is from control-state reachability for communicating finite-state machines with one perfect FIFO channel, which is undecidable because the channel can hold a Turing machine tape. The PLCS has a lossy copy of the perfect channel and two further channels. Each send of the perfect machine is simulated by many retransmissions of the message, and each receive by a loop that consumes all copies, so a computation of the perfect machine is simulated faithfully with positive probability. A second protocol restarts the simulation from time to time. Together these give: $s_F$ is reached with probability $1$ iff $s_F$ is reachable in the perfect machine. A good expansion links a page for the undecidability of control-state reachability in channel machines with perfect channels.

## Sources

- Parosh Aziz Abdulla, Christel Baier, S. Purushothaman Iyer and Bengt Jonsson, "Simulating perfect channels with probabilistic lossy channels", *Information and Computation* 197(1–2):22–40, 2005, doi:10.1016/j.ic.2004.12.001; read in the authors' archived manuscript of the journal version at <https://www.it.uu.se/research/docs/fm/apv/publications/files/plcs_detailed.ps>: Section 2 (communicating finite-state machines, Theorem 2), Section 3 (Definitions 3 and 4 and the problem Reach-PLCS), Section 4 and Theorem 18 of that copy. A preliminary version appeared in CONCUR 2000, Lecture Notes in Computer Science 1877, pp. 320–333, doi:10.1007/3-540-44618-4_24.
