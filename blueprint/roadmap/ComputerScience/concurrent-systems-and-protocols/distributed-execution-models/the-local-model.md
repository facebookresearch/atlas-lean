# The LOCAL model

In the LOCAL model of distributed computing, the network is a simple graph $G$ on a finite set $V$ of $n$ nodes, each of them a processor. The nodes carry unique identifiers from a range polynomial in $n$: an injective map $\mathrm{id} : V \to \{1, \dots, n^c\}$, for a constant $c \in \mathbb{N}$. For $c = 0$ the range is $\{1\}$, so only networks of at most one node have identifiers. Each node $v$ also has an input $x(v)$ from a set $I$.

An [algorithm](local-algorithm.md) $A$, the same at every node, has a set $S$ of states, a set $M$ of messages and a set $O$ of outputs, and consists of maps $\mathrm{init} : \mathbb{N} \times I \to S$, $\mathrm{send} : S \times \mathbb{N} \to M$, $\mathrm{update} : S \times \mathcal{M}(M) \to S$ and $\mathrm{out} : S \to O$, where $\mathcal{M}(M)$ is the set of finite multisets of elements of $M$. These sets and maps are arbitrary, so messages have unbounded size and the local computation is unrestricted.

Computation proceeds in synchronous rounds. The node $v$ starts in the state $\mathrm{init}(\mathrm{id}(v), x(v))$. In each round, every node $u$, in state $s_u$, sends the message $\mathrm{send}(s_u, \mathrm{id}(w))$ to each neighbour $w$; then every node $v$ receives the multiset $m_v$ of the messages its neighbours sent it and moves to the state $\mathrm{update}(s_v, m_v)$.

A $t$-round algorithm, for a function $t : \mathbb{N} \to \mathbb{N}$, is one in which every node outputs after $t(n)$ rounds: the output of the node $v$ is $\mathrm{out}(s)$, where $s$ is the state of $v$ after $t(n)$ rounds. Its complexity is $t$ as a function of $n$.

**Relation to the sources.** Linial's processors know their own identifiers at time zero, pass messages of unrestricted size to each neighbour in every synchronous time unit, and compute without restriction; his identifiers are positive integers, in most cases a bijection onto $\{1, \dots, n\}$, which is the case $c = 1$ here. The range $\{1, \dots, n^c\}$ is Suomela's, who fixes a constant $c > 1$. Problems without inputs are the case of a one-point set $I$.

A node starts knowing only its identifier and its input. Unlike in Suomela's model, it does not know its degree, and there are no port numbers. The maps of $A$ do not take $n$, but $A$ is a parameter, so a statement may choose the algorithm depending on $n$ or on $G$; Linial's lower bounds hold even if every processor knows $G$ in advance, and only the identifiers are unknown. Choosing the algorithm after seeing the identifiers or the inputs is a different matter: such an algorithm could store a colouring for the given identifiers and output it in zero rounds. The run is stopped from outside after $t(n)$ rounds, so the output can depend on $t(n)$: a node that counts rounds outputs $t(n)$, which is $n$ when $t$ is the identity, even on a graph with no edges.

Messages are addressed by the identifier of their recipient. This is no stronger than sending every neighbour the same message: a node in state $s$ can send the map $j \mapsto \mathrm{send}(s, j)$, and the recipient, keeping its identifier in its state, applies it to its own identifier, with the same outputs. This is an equality of outputs in this abstract round model, in which a message may be any value, a function included; it is not a finite-bit encoding or an effective implementation. When states can be encoded and $\mathrm{send}$ is computable, a node can send its encoded state instead, and the recipient evaluates $\mathrm{send}$ at its own identifier. Messages are received as a multiset, without the senders; a node can include its own identifier in its messages.

## Related topics

- [Locality of the output of a $t$-round algorithm](output-congr-ball.md): the output of a node is determined by the identifiers and inputs within distance $t(n)$ of it and by the neighbours of the nodes within distance less than $t(n)$.

## Sources

- N. Linial, "Locality in distributed graph algorithms", *SIAM Journal on Computing* 21(1):193–201, 1992: §1.
- J. Suomela, *Distributed Algorithms*, online textbook, 2014–2019, Aalto University (PDF version of 2 January 2021), <https://jukkasuomela.fi/da/>: §4.3.1 (a node's state machine depends on its degree and has one message per port) and §5.1 (identifiers).
