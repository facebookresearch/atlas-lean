# Undecidability of reachability for timed automata with one stopwatch

Reachability is undecidable for timed automata extended with one stopwatch: there is no algorithm that, given a timed
automaton with one additional variable whose rate is $0$ or $1$ in each location and which need not be reset when its rate changes,
together with a target location, decides whether the target is reachable (Henzinger, Kopke, Puri and Varaiya). The proof is
an effective reduction from the halting problem for two-counter machines that encodes the counter value $u$ as the clock value $2^{-u}$,
with gadgets for increment, decrement and zero test, respecting the source model's guards and resets; the machine halts if
and only if the target is reachable.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Turing machine.
- Proof prerequisite: Minsky: two-counter machines are universal.

## Depends on

- [Rectangular and initialized rectangular automata](rectangular-and-initialized-rectangular-automata.md)

## Sources

- What's Decidable About Hybrid Automata? — T. A. Henzinger, P. W. Kopke, A. Puri, P. Varaiya, UC Berkeley Memorandum UCB/ERL M98/22 (preliminary version STOC 1995), Abstract; Sec. 1; Sec. 4.1, Theorem 4.1 and its proof (case of slopes $k_1 \ne 0$ and $k_2 = 0$). <https://www2.eecs.berkeley.edu/Pubs/TechRpts//1998/ERL-98-22.pdf>
