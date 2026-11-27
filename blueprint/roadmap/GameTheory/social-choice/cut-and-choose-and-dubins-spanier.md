# Cut-and-choose and Dubins-Spanier

In the Robertson–Webb model with normalized nonatomic valuations:

1. for $n = 2$, cut and choose (agent 1 cuts the cake into two pieces of value $1/2$ to her with one cut query, agent 2 picks the
   piece she prefers after one evaluation query) yields an allocation that is proportional and envy-free, and for two agents every
   proportional allocation is envy-free;
2. for general $n$, the discrete Dubins–Spanier protocol (in each round every remaining agent makes a cut query for value $1/n$ from
   the current left end, the agent with the leftmost mark takes that piece and leaves) returns a proportional allocation with contiguous
   pieces using $O(n^2)$ queries.

The continuous moving-knife description is not itself a query count.

## Depends on

- [Cake cutting in the Robertson-Webb query model](cake-cutting-in-the-robertson-webb-query-model.md)

## Sources

- A. Procaccia, Harvard CS 1360 (Spring 2025), Lecture 10 notes: Cake Cutting, §1 (the model), Theorem 1 (for two agents an allocation is proportional if and only if it is envy-free), §3.1 (the Robertson–Webb queries), §3.2.1 (cut and choose with one cut query and one evaluation query) and §3.2.2 (the Dubins–Spanier moving knife and its query form, with $n + (n-1) + \dots + 2$ cut queries). In that query form each remaining agent cuts at value $1/\lvert N \rvert$ for the current set $N$ of remaining agents; proportionality needs the value $1/n$ for the original number $n$ of agents, as stated above: with three agents whose valuations are uniform, cuts at $1/\lvert N \rvert$ leave the last agent a piece of value $1/6$. <https://procaccia.info/courses/CS1360-S25/notes10.pdf>
