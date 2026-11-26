# Unit resolution and SAT-solver states

Let $\Delta$ be a CNF formula. *Unit resolution* repeatedly resolves a unit clause against the clauses containing the complement of its literal. Write $\Delta \vdash \ell$ when unit resolution derives the unit clause $\ell$ from $\Delta$, and $\Delta \vdash \mathrm{false}$ when it derives the empty clause; $\Delta$ is *1-inconsistent* if $\Delta \vdash \mathrm{false}$ and *1-consistent* otherwise.

A *decision sequence* is a sequence $D = \langle \ell_1, \dots, \ell_k \rangle$ of literals, $\ell_i$ being the decision at level $i$, and $D_m$ is its prefix of length $m$. A *SAT state* is a triple $S = (\Delta, \Gamma, D)$ of CNF formulas $\Delta$ (the input) and $\Gamma$ (the learned clauses) with $\Delta \models \Gamma$ and a decision sequence $D$; $S$ is 1-inconsistent when $\Delta \wedge \Gamma \wedge D$ is, and $S_k$ is $(\Delta, \Gamma, D_k)$. A literal $\ell$ is *implied at level* $k$, $S \vdash_k \ell$, if $k$ is the least integer with $\Delta \wedge \Gamma \wedge D_k \vdash \ell$. A state is *normal* if, for every $i \le k$, $S_{i-1}$ is 1-consistent and neither $\ell_i$ nor its complement is implied by $S_{i-1}$: no decision is made in a conflict or on an assigned variable.

## Sources

- K. Pipatsrisawat and A. Darwiche, "On the power of clause-learning SAT solvers with restarts", revised version of the paper in *Principles and Practice of Constraint Programming (CP 2009)*, LNCS 5732, Springer, 2009, pp. 654–668, <http://reasoning.cs.ucla.edu/fetch.php?id=101&type=pdf>, Section 3.1: the clause-learning algorithm, decision sequences, SAT states, 1-consistency, implication levels and normal states.
