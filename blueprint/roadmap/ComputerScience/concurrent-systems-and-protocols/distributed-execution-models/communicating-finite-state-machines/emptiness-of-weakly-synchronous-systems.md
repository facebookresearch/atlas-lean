# Emptiness of weakly synchronous systems with three machines is undecidable

Weakly synchronous executions of communicating machines proceed in phases in which every machine first sends and then receives. For point-to-point FIFO communication, deciding whether such a system with three machines has any accepting execution is undecidable, and the same holds under causally ordered communication.

**Setting (Di Giusto, Ferré, Lozes and Nisse).** Fix finite sets of processes and messages. A point-to-point message sequence chart (MSC) is a finite set of send events $!p\,q\,m$ and receive events $?p\,q\,m$ ($p \ne q$), totally ordered on each process, with a matching relation from sends to receives such that every receive has a unique matching send, the union of process order and matching is acyclic, and messages from $p$ to $q$ are received in the order sent (FIFO). An MSC is *weakly synchronous* if it is a concatenation $M_1 \cdots M_n$ in which, within each $M_i$, the set of send events is downward closed for the causal order of $M_i$. A *communicating system* has, for each process $p$, a finite transition system over the actions of $p$ with an initial and a final state; an *accepting run* on an MSC labels each event by a transition of its process so that each process goes from its initial to its final state and every message sent is received. The system is *weakly synchronous* if every MSC of its language is weakly synchronous, and the *emptiness problem* asks whether its language is empty.

**Theorem (Di Giusto, Ferré, Lozes and Nisse).** The emptiness problem for weakly synchronous point-to-point communicating systems with three processes is undecidable.

The input is promised to be weakly synchronous. Since an MSC is weakly synchronous and causally ordered exactly when it is weakly synchronous and point-to-point, the emptiness problem for weakly synchronous causally ordered systems with three processes is undecidable as well. Three is the threshold: with two machines every point-to-point MSC is also a mailbox MSC and reachability is decidable, as it is for weakly synchronous systems with mailbox communication; undecidability for four or more machines had been shown earlier.

## Depends on

None.

## Proof depends on

None.

## Expansion

The reduction is from emptiness of FIFO automata, finite-state machines with one FIFO queue, undecidable by Finkel and Lozes. A FIFO automaton is turned into a weakly synchronous system of three processes $a$, $b$, $c$ in which $a$ follows the automaton's transitions and sends its enqueued messages to both $b$ and $c$, and the other two processes are forced to forward messages in matching orders; the paper proves that the FIFO automaton has an accepting run if and only if the three-process system does. The construction is guided by an earlier result of the paper that the treewidth of weakly synchronous point-to-point MSCs is unbounded, witnessed by MSCs with arbitrarily large grids as minors. Emptiness of FIFO automata has no page here.

## Sources

- Cinzia Di Giusto, Davide Ferré, Étienne Lozes and Nicolas Nisse, "Weakly Synchronous Systems with Three Machines Are Turing Powerful", Reachability Problems (RP 2023), Lecture Notes in Computer Science 14235, pp. 28–41, Springer, 2023, <https://doi.org/10.1007/978-3-031-45286-4_3>; the definitions of Section 2 (MSCs, weakly synchronous MSCs, communicating systems and emptiness), the main theorem and its corollary in Section 4, and the appendix on causally ordered MSCs of arXiv:2308.10578v1 (the copy read), <https://arxiv.org/abs/2308.10578v1>.
