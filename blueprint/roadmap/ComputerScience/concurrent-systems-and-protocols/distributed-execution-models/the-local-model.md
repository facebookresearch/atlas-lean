# The LOCAL model

In the LOCAL model of distributed computing, the network is a simple graph $G$ on a finite set $V$ of $n$ nodes, each of them a processor. The nodes carry unique identifiers from a range polynomial in $n$: an injective map $\mathrm{id} : V \to \{1, \dots, n^c\}$, for a constant $c \in \mathbb{N}$. Each node $v$ also has an input $x(v)$ from a set $I$.

An [algorithm](local-algorithm.md) $A$, the same at every node, has a set $S$ of states, a set $M$ of messages and a set $O$ of outputs, and consists of maps $\mathrm{init} : \mathbb{N} \times I \to S$, $\mathrm{send} : S \times \mathbb{N} \to M$, $\mathrm{update} : S \times \mathcal{M}(M) \to S$ and $\mathrm{out} : S \to O$, where $\mathcal{M}(M)$ is the set of finite multisets of elements of $M$. These sets and maps are arbitrary, so messages have unbounded size and the local computation is unrestricted.

Computation proceeds in synchronous rounds. The node $v$ starts in the state $\mathrm{init}(\mathrm{id}(v), x(v))$. In each round, every node $u$, in state $s_u$, sends the message $\mathrm{send}(s_u, \mathrm{id}(w))$ to each neighbour $w$; then every node $v$ receives the multiset $m_v$ of the messages its neighbours sent it and moves to the state $\mathrm{update}(s_v, m_v)$.

A $t$-round algorithm, for a function $t : \mathbb{N} \to \mathbb{N}$, is one in which every node outputs after $t(n)$ rounds: the output of the node $v$ is $\mathrm{out}(s)$, where $s$ is the state of $v$ after $t(n)$ rounds. Its complexity is $t$ as a function of $n$.

**Relation to the sources.** Linial's processors know their own identifiers at the start, pass messages of unrestricted size to each neighbour in every synchronous time unit, and compute without restriction; his identifiers are positive integers, in most cases a bijection onto $\{1, \dots, n\}$, which is the case $c = 1$ here. The range $\{1, \dots, n^c\}$ is Suomela's, who fixes a constant $c > 1$. Problems without inputs are the case of a one-point set $I$. Messages are addressed by the identifier of their recipient and received as a multiset, without the senders; a node can include its own identifier in its messages.

## Related topics

- [Locality of the output of a $t$-round algorithm](output-congr-ball.md): the output of a node is determined by the identifiers and inputs within distance $t(n)$ of it and by the neighbours of the nodes within distance less than $t(n)$.

## Sources

- N. Linial, "Locality in distributed graph algorithms", *SIAM Journal on Computing* 21(1):193–201, 1992: §1.
- J. Suomela, *Distributed Algorithms*, Aalto University, 2021, <https://jukkasuomela.fi/da/>: §5.1.
