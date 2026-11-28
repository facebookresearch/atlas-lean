# Auxiliary variables of a parallel program

A set $A$ of program variables is a set of auxiliary variables of a program $S$ if its variables occur in $S$ only in assignments to variables of $A$: they record information about the run but never influence control flow or the values of the other variables. $S_A$ deletes those assignments.

Consider while programs with atomic regions and top-level parallel composition: component programs are built from $\mathbf{skip}$, assignments $u := t$, sequencing, $\mathbf{if}\ B\ \mathbf{then}\ S_1\ \mathbf{else}\ S_2\ \mathbf{fi}$, $\mathbf{while}\ B\ \mathbf{do}\ S\ \mathbf{od}$ and $\mathbf{await}\ B\ \mathbf{then}\ T\ \mathbf{end}$ with a body $T$ containing neither loops nor $\mathbf{await}$; $\langle T \rangle$ abbreviates $\mathbf{await}\ \mathrm{true}\ \mathbf{then}\ T\ \mathbf{end}$, and a parallel program combines components $[S_1 \parallel \dots \parallel S_n]$, possibly inside sequencing, conditionals and loops.

**Definition.** A set $A$ of simple variables is a *set of auxiliary variables* of a program $S$ if every occurrence in $S$ of a variable of $A$ lies in an assignment $u := t$ whose left-hand side $u$ belongs to $A$. In particular no variable of $A$ occurs in a Boolean guard of a conditional, loop or $\mathbf{await}$, nor in the right-hand side of an assignment to a variable outside $A$.

$S_A$ is the program obtained from $S$ by deleting every assignment to a variable of $A$, using $\mathbf{skip}$ where a statement becomes empty.

Auxiliary variables are ordinary program variables of $S$: they may be assigned during a run and appear in the states the assertions of a proof outline describe. They are not the logical (specification) variables that a Hoare triple may use to name initial values, which no program assigns. Whether a variable is auxiliary depends on the program: a variable read by a guard is never auxiliary, and the empty set is a set of auxiliary variables of every program.

## Depends on

None.

## Proof depends on

None.

## Expansion

A development fixes the syntax of terms and Boolean expressions with their free-variable functions and the deletion map $S \mapsto S_A$ by structural recursion, including deletion inside $\mathbf{await}$ bodies.

## Sources

- K. R. Apt and E.-R. Olderog, "Fifty years of Hoare's logic", *Formal Aspects of Computing* 31(6):751–807, 2019, <https://doi.org/10.1007/s00165-019-00501-3>, author version arXiv:1904.03917v1, <https://arxiv.org/abs/1904.03917v1>: Section 8.1 (definition of a set of auxiliary variables, the AUXILIARY VARIABLES rule and the await statement).
- S. de Gouw and J. Rot, "Effectively eliminating auxiliaries", in *Theory and Practice of Formal Methods: Essays Dedicated to Frank de Boer on the Occasion of His 60th Birthday*, LNCS 9660, Springer, 2016, pp. 226–241, <https://doi.org/10.1007/978-3-319-30734-3_16>, author copy <http://jurriaan.creativecode.org/wp-content/uploads/2013/04/ghost.pdf>: Section 2 (notation $(S)_{\bar z}$ and Definition 1) and Section 2.1.
- L. Prensa Nieto, "Completeness of the Owicki-Gries system for parameterized parallel programs", in *Proceedings 15th International Parallel and Distributed Processing Symposium (IPDPS 2001)*, workshop on Formal Methods for Parallel Programming: Theory and Applications, IEEE, 2001, pp. 1534–1541, <https://doi.org/10.1109/IPDPS.2001.925138>, author copy <https://www-sop.inria.fr/lemme/Leonor.Prensa/publications/Compl.ps.gz>: Section 2.1 (await bodies without loops or await, $\langle S \rangle$).
