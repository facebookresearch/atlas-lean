# Broadcast protocols and their networks

A broadcast protocol is a finite-state machine whose transitions broadcast or receive messages. Its network runs any number of identical copies: one process broadcasts, every other process that can receive the message takes a reception transition, and the rest stay put.

**Protocols.** For a finite alphabet $\Sigma$ of messages write $!!\Sigma = \{!!a \mid a \in \Sigma\}$ (broadcasts), $?\Sigma = \{?a \mid a \in \Sigma\}$ (receptions) and $\mathrm{Op}_\Sigma = !!\Sigma \cup ?\Sigma$. A *protocol* is a tuple $\mathcal{P} = (Q, \Sigma, q_{in}, T)$ with a finite set $Q$ of states, a finite set $\Sigma$ of messages, an initial state $q_{in} \in Q$ and a set of transitions $T \subseteq Q \times \mathrm{Op}_\Sigma \times Q$. For $q \in Q$ let $R(q) = \{a \in \Sigma \mid (q, ?a, q') \in T \text{ for some } q'\}$ be the messages receivable in $q$.

**Configurations.** For $n \ge 1$, an $n$-process configuration is a vector $C \in Q^n$, where $C(e)$ is the state of process $e$; its size is $\lVert C \rVert = n$. It is *initial* if $C(e) = q_{in}$ for every $e$. The number of processes is arbitrary but fixed along an execution.

**Steps.** For configurations $C, C'$ of the same size $n$, a transition $t = (q, !!a, q') \in T$ and a process $e$, write $C \xrightarrow{e, t} C'$ if $C(e) = q$, $C'(e) = q'$, and every other process $e'$ either receives, $(C(e'), ?a, C'(e')) \in T$, or cannot receive $a$, in which case $a \notin R(C(e'))$ and $C'(e') = C(e')$. So a broadcast is received by every process able to receive it, and a process able to receive it cannot ignore it. Write $C \to C'$ if $C \xrightarrow{e, t} C'$ for some $e$ and $t$, and $\to^\ast$ for the reflexive transitive closure.

**Executions.** A finite (infinite) execution is a finite (infinite) sequence $C_0 C_1 \cdots$ of configurations with $C_0$ initial and $C_{i-1} \to C_i$ for every $i > 0$.

A protocol is *Wait-Only* if no state has both an outgoing broadcast and an outgoing reception. This is the network model of Esparza, Finkel and Mayr, in which every process hears every broadcast.

## Depends on

None.

## Proof depends on

None.

## Expansion

The model is a parameterized system: verification questions quantify over the number of processes, so the state space is infinite even though each process is finite-state. Counting how many processes sit in each state encodes rendezvous protocols in a vector addition system with states, but the encoding fails for broadcasts: a broadcast must be received by all processes in a given state, a bulk transfer of a counter value that classical vector addition systems cannot express without transfer arcs. Rendezvous communication can be simulated by broadcasts.

## Sources

- Lucie Guillou, Arnaud Sangnier and Nathalie Sznajder, "Wait-Only Broadcast Protocols Are Easier to Verify", 50th International Symposium on Mathematical Foundations of Computer Science (MFCS 2025), Leibniz International Proceedings in Informatics (LIPIcs) 345, pp. 53:1–53:17, 2025, <https://doi.org/10.4230/LIPIcs.MFCS.2025.53>. Read in arXiv:2506.22144v1, <https://arxiv.org/abs/2506.22144v1>; Definition 2.1 and Section 2.1 (networks of processes using broadcast communication), numbering of arXiv:2506.22144v1.
- Javier Esparza, Alain Finkel and Richard Mayr, "On the Verification of Broadcast Protocols", Proceedings of the 14th Annual IEEE Symposium on Logic in Computer Science (LICS 1999), pp. 352–359, 1999, <https://doi.org/10.1109/LICS.1999.782630> (the origin of the model, cited as in the first source).
