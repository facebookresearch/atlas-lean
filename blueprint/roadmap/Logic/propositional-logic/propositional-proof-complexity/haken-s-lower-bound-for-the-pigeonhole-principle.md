# Haken's lower bound for the pigeonhole principle

For $n \ge 1$ let $\mathrm{PHP}^{n+1}_n$ be the CNF formula with variables $p_{i,j}$ ($i \le n+1$, $j \le n$), the clauses $\bigvee_{j} p_{i,j}$ for each pigeon $i$ and $\neg p_{i,j} \vee \neg p_{i',j}$ for each hole $j$ and pigeons $i \ne i'$. There is a constant $c > 0$ such that every resolution refutation of $\mathrm{PHP}^{n+1}_n$ contains at least $2^{c n}$ clauses.

## Expansion

This page becomes ready once these prerequisites are stated:

- Size of general (DAG-like) resolution refutations (statement prerequisite; not yet stated)

## Sources

- A. Haken, "The intractability of resolution", *Theoretical Computer Science* 39:297–308, 1985
- J. Nordström, *Computational Complexity* (2023), scribe notes for Lecture 20, <https://jakobnordstrom.se/teaching/CoCo23/lecturenotes/ScribeNotesLec20.pdf>
