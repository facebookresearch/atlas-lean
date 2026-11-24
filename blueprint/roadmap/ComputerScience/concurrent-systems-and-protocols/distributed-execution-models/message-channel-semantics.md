# Message channel semantics

In the [asynchronous message-passing model](asynchronous-message-passing-systems.md), the channel from process $p$ to process $q$ determines which sequences of send and deliver events it admits. The common variants are as follows. Here a *correct* process is one that does not crash, and so takes infinitely many steps.
- **Perfect (reliable) link.** It satisfies three properties:
    - *reliable delivery*: if a correct $p$ sends $m$ to a correct $q$, then $q$ eventually delivers $m$;
    - *no duplication*: no message is delivered more than once;
    - *no creation*: every delivery of $m$ from $p$ at $q$ is preceded by a send of $m$ from $p$ to $q$.

    The channel state is a multiset of messages in transit, and delivery order is arbitrary.
- **FIFO link.** A reliable link that also delivers the messages from $p$ to $q$ in the order they were sent. Its state is a queue.
- **Fair-loss link.** It satisfies three properties:
    - *fair loss*: if a correct $p$ sends $m$ to a correct $q$ infinitely often, then $q$ delivers $m$ infinitely often;
    - *finite duplication*: a message sent finitely often is delivered only finitely often;
    - *no creation*, as above.

    Messages may be dropped by a loss event.
- **Stubborn link.** It satisfies two properties:
    - *stubborn delivery*: if a correct $p$ sends $m$ once to a correct $q$, then $q$ delivers $m$ infinitely often;
    - *no creation*, as above.

    Retransmitting every message forever over a fair-loss link implements a stubborn link. Delivering only the first copy of each message, identified by a sequence number, then gives a perfect link.
- **Duplicating link.** It may re-deliver any message from the history of sent messages, which never shrinks.

The safety properties, such as no creation, no duplication and FIFO order, constrain finite prefixes of executions. Reliable delivery, fair loss and stubborn delivery are *liveness* properties of infinite executions, $\omega$-properties, and cannot be expressed by the one-step transition relation of the channel alone.

## Depends on

- [Asynchronous message-passing systems](asynchronous-message-passing-systems.md)

## Expansion

This page becomes ready once:

- The statement must be checked against the cited sources

## Sources

- *CS-451 Distributed Algorithms*, course notes on the EPFL course of that name, <https://www.kjaer.io/distributed-algorithms/>: fair-loss links (properties FLL1–FLL3), stubborn links (SL1–SL2) with their implementation by retransmitting forever over a fair-loss link, perfect links (PL1–PL3), and FIFO order. The notes follow C. Cachin, R. Guerraoui and L. Rodrigues, *Introduction to Reliable and Secure Distributed Programming*, 2nd ed., Springer, 2011.
