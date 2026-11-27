# Envy-cycle elimination yields EF1 allocations for monotone valuations

For $n$ agents with arbitrary monotone valuations over $m$ indivisible goods, the Lipton–Markakis–Mossel–Saberi procedure, which allocates goods one at a time to an unenvied agent and, when every agent is envied, rotates bundles backwards along a cycle of the envy graph, terminates with a complete allocation that is envy-free up to one good. It performs at most $m n (n - 1)$ cycle eliminations, and every agent's envy is bounded by its maximum marginal value of a single good.

## Proof sketch

Giving a good to an unenvied agent preserves EF1, since removing that good removes any new envy. Rotating along an envy cycle strictly increases the utilities of agents on the cycle, preserves EF1 and strictly decreases the number of envy edges, which bounds the number of rotations per good.

## Depends on

- [Is EF1](../../noncooperative-games/fair-division-of-indivisible-goods-ef1-via-envy/is-ef1.md)
- [Envy cycle](../../noncooperative-games/fair-division-of-indivisible-goods-ef1-via-envy/is-envy-cycle.md)

## Proof depends on

- [Existence of an EF1 allocation with acyclic envy graph](../../noncooperative-games/fair-division-of-indivisible-goods-ef1-via-envy/exists-ef1-acyclic.md)

## Sources

- Richard J. Lipton, Evangelos Markakis, Elchanan Mossel and Amin Saberi, "On Approximately Fair Allocations of Indivisible Goods", Proceedings of the 5th ACM Conference on Electronic Commerce (EC 2004), 2004.
- Benjamin Plaut and Tim Roughgarden, "Almost Envy-Freeness with General Valuations", SIAM Journal on Discrete Mathematics, 2020.
