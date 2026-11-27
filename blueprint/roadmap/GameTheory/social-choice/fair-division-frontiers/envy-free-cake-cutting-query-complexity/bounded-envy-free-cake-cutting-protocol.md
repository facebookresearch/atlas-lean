# A discrete and bounded envy-free cake cutting protocol for any number of agents

In the Robertson–Webb query model, with $n$ agents having valuations on the cake $[0, 1]$ that are non-negative, additive over disjoint pieces and divisible (every interval contains a subinterval of any prescribed fraction of its value), there is a deterministic discrete protocol that always outputs an envy-free allocation of the whole cake (pieces being finite unions of intervals) and whose number of queries is bounded by a function of $n$ alone, namely at most $n^{n^{n^{n^{n^{n}}}}}$. For four agents there is such a protocol using a bounded number of queries independent of the valuations.

## Proof sketch

The protocol repeatedly runs a core subprotocol in which a cutter divides the residue into equal parts and the other agents trim pieces, obtaining a partial envy-free allocation in which some agent dominates another (would not envy them even if the other received the entire residue). Domination relations are monotone and accumulate; once a large enough set of dominations is present the residue can be allocated recursively among the non-dominated agents. Bounding the number of rounds needed to collect dominations gives the tower bound.

## Depends on

- [Cake cutting in the Robertson-Webb query model](../../cake-cutting-in-the-robertson-webb-query-model.md)

## Sources

- H. Aziz, S. Mackenzie, "A Discrete and Bounded Envy-Free Cake Cutting Protocol for Any Number of Agents", FOCS 2016, arXiv:1604.03655.
- H. Aziz, S. Mackenzie, "A Discrete and Bounded Envy-Free Cake Cutting Protocol for Four Agents", STOC 2016, arXiv:1508.05143.
