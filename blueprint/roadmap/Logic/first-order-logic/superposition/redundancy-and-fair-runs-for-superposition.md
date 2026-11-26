# Redundancy and fair runs for superposition

Fix the clause ordering $\succ_C$ of the [superposition calculus](superposition-calculus.md), and let $G_\Sigma(N)$ be the set of ground instances of clauses of $N$ over its signature $\Sigma$, which has at least one constant symbol, so that every clause has ground instances. A ground clause $C$ is *redundant* with respect to a set $N$ of ground clauses if it follows from clauses of $N$ that are smaller than $C$; a clause is redundant with respect to a set $N$ of clauses if all its ground instances are redundant with respect to $G_\Sigma(N)$. $\mathrm{Red}(N)$ is the set of clauses redundant with respect to $N$. The set $N$ is *saturated up to redundancy* if the conclusion of every inference from clauses in $N \setminus \mathrm{Red}(N)$ belongs to $N \cup \mathrm{Red}(N)$.

A *run* is a sequence $N_0 \vdash N_1 \vdash N_2 \vdash \cdots$ of sets of clauses with $N_i \models N_{i+1}$ and every clause of $N_i \setminus N_{i+1}$ redundant with respect to $N_{i+1}$. Its *limit* is the set $N_\infty = \bigcup_i \bigcap_{j \ge i} N_j$ of persistent clauses. A run is *fair* if the conclusion of every inference from clauses in $N_\infty \setminus \mathrm{Red}(N_\infty)$ belongs to some $N_i \cup \mathrm{Red}(N_i)$.

## Depends on

- [Superposition calculus](superposition-calculus.md)

## Sources

- U. Waldmann, *Automated Reasoning II*, lecture notes, Max Planck Institute for Informatics, summer semester 2024, <https://rg1-teaching.mpi-inf.mpg.de/autrea2-ss24/notes-current.pdf>, Section 3.3, redundancy and saturation up to redundancy, p. 53, and Section 3.4, runs, limits and fairness, pp. 59–61.
