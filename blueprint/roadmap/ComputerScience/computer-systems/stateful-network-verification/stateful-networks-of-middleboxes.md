# Stateful networks of middleboxes

A stateful network connects hosts and finite-state middleboxes by directed packet channels; a configuration records each middlebox's state and the packets in transit, and the safety problem asks whether some middlebox can reach its error state.

**Networks.** A network $N = (H \cup M, E, P)$ has a finite set $P$ of packets (the source's packets are tuples of a fixed number of fields over finite sorts), a finite set $H$ of hosts (each with a set $P_h \subseteq P$ of packets it can send), a finite set $M$ of middleboxes (each with a set $C_m$ of ports) and a finite set $E$ of directed channels, each from a host or a middlebox port to a middlebox port or a host (a channel from a middlebox to itself is allowed); the graph is bidirected. As an input to an algorithm, a network is given by these finite sets and the transition tables of its middleboxes. Each middlebox $m$ is a transition system with a finite state set $\Sigma[m]$, an initial state $\sigma_I(m)$, a distinguished error state, and transitions $s \xrightarrow{(p, c)/(p_i, c_i)_{i = 1..k}} s'$: in state $s$, on reading packet $p$ from port $c$, move to $s'$ and emit $p_i$ on port $c_i$.

**Ordered semantics.** A configuration $(\sigma, \pi)$ maps each middlebox to a state and each channel to a finite sequence of packets; initially every middlebox is in $\sigma_I(m)$ and all channels are empty. A middlebox step takes the first packet $p$ of an ingress channel $e$ of $m$ (at port $c$), applies a transition of $m$ for $(p, c)$, removes $p$ from $e$ and appends each $p_i$ to the egress channel at port $c_i$; other middleboxes do not change. A host step appends a packet of $P_h$ to an egress channel of $h$ or removes the first packet from an ingress channel of $h$. A configuration is an error configuration if some middlebox is in its error state. Channels behave as FIFO queues.

**Variants.** In the *unordered* semantics a middlebox may read any packet in transit on an ingress channel, not only the first. In the *reverting* semantics a middlebox step may, instead of the target state of the transition, put the middlebox back into its initial state $\sigma_I(m)$; the ordered reverting and unordered reverting semantics combine these relaxations.

**Safety.** The *safety verification problem* for a semantics asks, given a network, whether no error configuration is reachable from the initial configuration.

## Depends on

None.

## Proof depends on

None.

## Expansion

Middleboxes model firewalls, load balancers, caches and similar devices whose forwarding depends on the history of packets seen. The relaxations are justified for many real middleboxes, whose behavior does not depend on packet order across channels or which can lose their state. Under the unordered semantics safety is decidable and EXPSPACE-complete (Velner and coauthors), because channels become multisets; the source designs abstract interpretations whose precision corresponds to these semantics.

## Sources

- Kalev Alpernas, Roman Manevich, Aurojit Panda, Mooly Sagiv, Scott Shenker, Sharon Shoham and Yaron Velner, "Abstract Interpretation of Stateful Networks", in *Static Analysis (SAS 2018)*, Lecture Notes in Computer Science 11002, Springer, 2018, pp. 86–106, <https://doi.org/10.1007/978-3-319-99725-4_8>; read as arXiv:1708.05904v3, <https://arxiv.org/abs/1708.05904v3>: Section 2 (the paragraph "Packets"), Section 3 ("Network Semantics": topology, ordered configurations and transitions, and the safety verification problem) and Section 3.3 (unordered and reverting semantics), in the numbering of that version.
