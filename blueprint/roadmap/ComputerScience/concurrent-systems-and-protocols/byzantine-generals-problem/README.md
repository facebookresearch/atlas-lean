# Byzantine generals problem

A commander sends an order to the other generals, some of whom, possibly including the commander, are traitors; the loyal generals must agree (IC1), on the commander's order if it is loyal (IC2). The oral-message model uses synchronous rounds, arbitrary Byzantine failures, and a complete network of reliable links on which receivers know the sender, but no signatures. With at least three generals and two orders it is solvable with at most $m$ traitors exactly when there are more than $3m$ generals.

The signed-message model instead uses ideal authentication. The agreement and validity result for its completed histories does not require that population bound.

- [Oral-message protocol](oral-protocol.md)
- [Local views determine states](states-eq-of-inbox-eq.md)
- [Initial state of a general](init-state.md)
- [Initial state of the commander](init-state-self.md)
- [Initial state of a lieutenant](init-state-of-ne.md)
- [Executions of an oral-message protocol](state.md)
- [Messages received in a round](inbox.md)
- [The start of an execution](state-zero.md)
- [One round of an execution](state-succ.md)
- [Decision of a general](decision.md)
- [Agreement condition (IC1)](agreement.md)
- [Validity in the Byzantine generals problem](validity.md)
- [Solving the Byzantine generals problem](solves.md)
- [No protocol for three generals tolerates one traitor](exists-violation-three.md)
- [No protocol for three generals solves the Byzantine generals problem with one traitor](not-solves-three.md)
- [Three generals simulating a protocol](simulate.md)
- [The simulation is faithful](state-simulate.md)
- [Simulation reduces many generals to three](solves-simulate.md)
- [No protocol for $n$ generals tolerates $m$ traitors when $3 \le n \le 3m$](not-solves-of-card-le-three-mul.md)
- [Majority of a multiset](majority.md)
- [A value filling more than half of a multiset is its majority](majority-eq-of-lt-count.md)
- [Majority falls back to the default value](majority-eq-default.md)
- [Value received from a commander](received.md)
- [The oral messages algorithm](om.md)
- [A loyal commander sends its value](received-of-loyal.md)
- [A traitorous commander sends the adversary's value](received-of-not-loyal.md)
- [A loyal commander is obeyed under oral messages](om-eq-of-loyal.md)
- [Validity under oral messages (IC2)](om-valid.md)
- [Agreement under oral messages (IC1)](om-agree.md)
- [Oral messages achieve interactive consistency](om-interactive-consistency.md)
- [The oral messages algorithm solves the Byzantine generals problem](byzantine-generals.md)
- [Traitor relays matching the protocol messages](adv-of-messages.md)
- [Relay of a traitor along an extended path](adv-of-messages-append-singleton.md)
- [The protocol runs the oral messages algorithm in the expected number of rounds](decision-to-protocol.md)
- [The protocol runs the oral messages algorithm](decision-to-protocol-of-le.md)
- [Oral messages, run as a protocol, solve the Byzantine generals problem](solves-to-protocol.md)
- [The oral messages algorithm as an oral-message protocol](to-protocol.md)
- [Solvability of the Byzantine generals problem with oral messages](exists-solves-iff-three-mul-lt-card.md)
- [Byzantine agreement with signed messages](byzantine-agreement-with-signed-messages.md)

## Signed-message model

- [Message](message.md)
- [Phase](phase.md)
- [Event](event.md)
- [History](history.md)
- [Initial](initial.md)
- [Relay](relay.md)
- [Proper](proper.md)
- [May Forward](may-forward.md)
- [Relay Target](relay-target.md)
- [Accepts](accepts.md)
- [Orders Before](orders-before.md)
- [Orders](orders.md)
- [Learns](learns.md)
- [Follows SM](follows-sm.md)
- [Choice](choice.md)
- [Decision](decision-2.md)
- [Orders eq](orders-eq.md)
- [Orders eq singleton](orders-eq-singleton.md)

## Related topics

- [Byzantine agreement](../byzantine-agreement/README.md): the version in which every process has an input (Fischer, Lynch and Merritt), reduced here to the commander version.
- [Paxos consensus](../paxos-consensus/README.md): consensus without synchrony but with only crash failures; Lamport's non-Byzantine counterpart.

## Sources

- L. Lamport, R. Shostak, M. Pease, *The Byzantine Generals Problem*, ACM Transactions on Programming Languages and Systems 4(3), July 1982, 382–401: Section 1 (the problem, IC1 and IC2, p. 384), Section 2 (impossibility with oral messages, pp. 384–386, footnote 1 on two generals), Section 3 (assumptions A1–A3, Algorithm OM(m), Lemma 1 and Theorem 1, pp. 387–390), and Section 4 (the signed-messages algorithm and Theorem 2).
