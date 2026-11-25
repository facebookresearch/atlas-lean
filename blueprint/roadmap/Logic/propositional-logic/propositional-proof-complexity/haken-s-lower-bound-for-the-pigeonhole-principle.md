# Haken's lower bound for the pigeonhole principle

For $n \ge 1$ let $\mathrm{PHP}^{n+1}_n$ be the CNF formula with variables $p_{i,j}$ ($i \le n+1$, $j \le n$), the clauses $\bigvee_{j} p_{i,j}$ for each pigeon $i$ and $\neg p_{i,j} \vee \neg p_{i',j}$ for each hole $j$ and pigeons $i \ne i'$.

A *resolution refutation* of a CNF formula is a sequence of clauses ending with the empty clause, each of which is a clause of the formula or the resolvent
$C \vee D$ of two earlier clauses $C \vee x$ and $D \vee \neg x$; its *length* is the number of clauses in the sequence.

**Theorem (Haken).** Resolution refutations of $\mathrm{PHP}^{n+1}_n$ have length $\exp(\Omega(n))$: there is a constant $c > 0$ such that every resolution refutation of
$\mathrm{PHP}^{n+1}_n$ contains at least $2^{c n}$ clauses.

## Sources

- J. Nordström, *Computability and Complexity 2022/23*, Lecture 20 scribe notes (scribe S. F. de Rezende), <https://jakobnordstrom.se/teaching/CoCo23/lecturenotes/ScribeNotesLec20.pdf>: the definition of the pigeonhole formulas (2.1a)–(2.1b), Theorem 2.1 with its proof, and the restatement that every refutation requires $2^{\delta n}$ steps for large $n$ (refutation length counted in clauses).
