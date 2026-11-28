# Weak closure and weak realizability of sets of MSCs

A set of message sequence charts is weakly realizable when every chart that any distributed implementation accepting the set must also accept already belongs to the set.

**Concurrent automata.** An implementation is a tuple of automata $A_1, \dots, A_n$, one per process. $A_i$ has a set $Q_i$ of states, not necessarily finite, a transition relation over the labels of the events of $P_i$ (the sends $\mathrm{send}(i, j, a)$ and receives $\mathrm{receive}(j, i, a)$), an initial state and a set of accepting states. For every ordered pair $(i, j)$ the product $\prod_i A_i$ has two FIFO buffers, words over $\Sigma$: a pending buffer for messages sent by $P_i$ and still in transit, and a receive buffer for messages that have reached $P_j$. A send by $P_i$ to $P_j$ appends the message to the end of the pending buffer. A silent transfer moves the first message of the pending buffer to the end of the receive buffer. A receive of $a$ from $P_i$ by $P_j$ is possible only when $a$ is at the front of the receive buffer, and removes it. The initial configuration has every component in its initial state and every buffer empty. A configuration is *accepting* when every component is in an accepting state and every buffer is empty. The product accepts a word over the event labels if some run reads it, silent transfers aside, from the initial configuration to an accepting configuration. It accepts an MSC if it accepts one of its linearizations, equivalently all of them.

**Weak closure.** A set $L$ of MSCs *weakly implies* an MSC $M$ if every tuple of automata whose product accepts all MSCs of $L$ also accepts $M$. Equivalently, for every $i$ there is $M_i \in L$ whose events on $P_i$ form the same sequence as those of $M$. The *weak closure* $L^w$ is the set of MSCs weakly implied by $L$, and $L$, or a graph $G$ with $L(G) = L$, is *weakly realizable* if $L = L^w$.

The automata in this definition have arbitrary state sets, as in the source, so a weakly realizable set need not be the language of any product of finite automata. For example, let $L$ consist of the charts in which $P_1$ sends $k$ copies of a message $a$ to $P_2$ and $P_2$ receives them, for every perfect square $k \ge 1$. $L$ passes the projection test, so it is weakly realizable. Yet a product of finite automata accepts such a chart with $k$ messages exactly when $k$ lies in both the sender's and the receiver's unary regular language, so the counts it accepts form a unary regular set, and the perfect squares do not.


## Depends on

- [MSC graphs](msc-graphs.md)

## Proof depends on

None.

## Expansion

*Safe realizability* asks for a stronger implementation. A configuration of the product is a *deadlock* if no accepting configuration is reachable from it, and the product is *deadlock-free* if no configuration reachable from its initial configuration is a deadlock. $L$ is safely realizable if $L$ is exactly the set of MSCs accepted by some deadlock-free product (Section 3.2 of the source). Weak realizability does not require deadlock-freedom.

For a finite set of MSCs, weak realizability is coNP-complete and safe realizability is decidable in polynomial time (Alur, Etessami and Yannakakis, ICSE 2000, as recalled in Section 3.1 of the source). For bounded MSC graphs, safe realizability is in EXPSPACE (Theorem 3 of the source).

## Sources

- Rajeev Alur, Kousha Etessami and Mihalis Yannakakis, "Realizability and verification of MSC graphs", *Theoretical Computer Science* 331(1):97–114, 2005, doi:10.1016/j.tcs.2004.09.034; read in the authors' manuscript of the journal version at <https://www.cis.upenn.edu/~alur/Icalp01.pdf>: Section 2.3 (concurrent automata, their product, initial and accepting states), Section 3.1 (weak implication, weak closure and weak realizability) and Section 3.2 (deadlock-freedom, safe realizability and Theorem 3) of that copy.
