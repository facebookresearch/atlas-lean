# Synchronizability of communicating machines

A system of communicating finite-state machines is synchronizable if its observable send behavior under unbounded FIFO channels coincides with its behavior under rendezvous communication, where each send is immediately received; language synchronizability compares send traces only.

**Messages and traces.** A message set $M = \langle \Sigma_M, n, \mathrm{src}, \mathrm{dst} \rangle$ has finitely many messages, $n \ge 1$ peers, and for each message $a$ peers $\mathrm{src}(a) \ne \mathrm{dst}(a)$ in $\{1, \dots, n\}$. Actions are sends $!a$ (by peer $\mathrm{src}(a)$) and receives $?a$ (by peer $\mathrm{dst}(a)$); traces are finite sequences of actions. A trace is FIFO if in every prefix, for all peers $i \ne j$, the sequence of messages received by $j$ from $i$ is a prefix of the sequence of messages sent by $i$ to $j$; it is $k$-bounded FIFO if moreover at most $k$ messages are pending in each channel at every prefix, and synchronous if it has the form $!a_1\, ?a_1 \cdots !a_\ell\, ?a_\ell$. A trace is stable if every channel is empty at its end.

**Systems.** A system is $\mathcal{S} = (\mathcal{M}_1, \dots, \mathcal{M}_n)$ where each peer $\mathcal{M}_i$ is a finite automaton, all states accepting, over the actions of peer $i$. A configuration consists of a state of each peer and the content $w_{i,j} \in \Sigma_M^*$ of each channel $i \to j$ (peer-to-peer semantics: one FIFO channel per ordered pair of distinct peers); a send by $i$ to $j$ appends to $w_{i,j}$, a receive by $j$ from $i$ removes the head of $w_{i,j}$. The initial configuration has initial states and empty channels. A trace of $\mathcal{S}$ is a trace executable from the initial configuration, equivalently a FIFO trace whose projection on each peer $i$ is accepted by $\mathcal{M}_i$. $\mathit{Tr}_k(\mathcal{S})$ is the set of $k$-bounded traces for $k \ge 1$, $\mathit{Tr}_0(\mathcal{S})$ the set of synchronous traces, and $\mathit{Tr}(\mathcal{S}) = \bigcup_{k \ge 0} \mathit{Tr}_k(\mathcal{S})$.

**Synchronizability.** For a trace $\tau$ let $\tau{\upharpoonright}!$ be its sequence of sent messages. Let $\mathit{sTr}^{w}_k(\mathcal{S}) = \{\tau{\upharpoonright}! \mid \tau \in \mathit{Tr}_k(\mathcal{S})\}$ and $\mathit{sTr}_k(\mathcal{S}) = \mathit{sTr}^{w}_k(\mathcal{S}) \cup \{(\tau{\upharpoonright}!, \gamma) \mid \tau \in \mathit{Tr}_k(\mathcal{S})$ leads to the stable configuration $\gamma\}$, and define $\mathit{sTr}$ and $\mathit{sTr}^{w}$ likewise from $\mathit{Tr}(\mathcal{S})$. $\mathcal{S}$ is synchronizable if $\mathit{sTr}_0(\mathcal{S}) = \mathit{sTr}(\mathcal{S})$, and language synchronizable if $\mathit{sTr}^{w}_0(\mathcal{S}) = \mathit{sTr}^{w}(\mathcal{S})$.

## Depends on

None.

## Proof depends on

None.

## Expansion

Synchronizability was introduced by Basu and Bultan, as the source recalls (Section 1), as a sufficient condition for reducing the verification of asynchronously communicating peers to synchronous ones; for the peer-to-peer semantics it had been claimed decidable. The source refutes that claim with a counterexample, proves undecidability, and recovers decidability for systems whose communication topology is an oriented ring, where synchronizability coincides with $1$-synchronizability ($\mathit{sTr}_0 = \mathit{sTr}_1$).

## Sources

- Alain Finkel and Etienne Lozes, "Synchronizability of communicating finite state machines is not decidable", *Logical Methods in Computer Science* 19(4), article 33, 2023, <https://doi.org/10.46298/lmcs-19(4:33)2023>; read as arXiv:1702.07213v7, <https://arxiv.org/abs/1702.07213v7>, the journal version: Section 1 (the origin of synchronizability) and Section 2 (message sets, traces, FIFO and bounded traces, peers, systems and configurations, and the definition of synchronizability with its sets of send traces).
