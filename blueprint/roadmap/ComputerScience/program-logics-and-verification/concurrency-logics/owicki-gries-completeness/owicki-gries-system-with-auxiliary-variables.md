# Owicki–Gries proof system with auxiliary variables

The Owicki–Gries system is defined for partial correctness of shared-variable parallel programs: Hoare's rules for components, a rule for atomic regions, a parallel rule over interference-free proof outlines, and a rule that deletes auxiliary variables added to the program for the proof.

Use the programs and the sets of [auxiliary variables](auxiliary-variables-of-a-parallel-program.md) $A$ with the deleted programs $S_A$, over a first-order assertion language interpreted in a fixed structure; a triple $\{p\}\,S\,\{q\}$ is *valid* if every terminating computation of $S$ from a state satisfying $p$ ends in a state satisfying $q$, computations of $[S_1 \parallel \dots \parallel S_n]$ interleaving the atomic steps of the components (an assignment, a guard evaluation, or a whole $\mathbf{await}$ whose guard holds). The system $\mathcal{O}$ has these rules:

- *Sequential rules* (the proof system for while programs): $\{p\}\,\mathbf{skip}\,\{p\}$; $\{p[u := t]\}\,u := t\,\{p\}$; from $\{p\}\,S_1\,\{r\}$ and $\{r\}\,S_2\,\{q\}$ infer $\{p\}\,S_1; S_2\,\{q\}$; from $\{p \wedge B\}\,S_1\,\{q\}$ and $\{p \wedge \neg B\}\,S_2\,\{q\}$ infer the conditional; from $\{p \wedge B\}\,S\,\{p\}$ infer $\{p\}\,\mathbf{while}\ B\ \mathbf{do}\ S\ \mathbf{od}\,\{p \wedge \neg B\}$; consequence, from $p \to p_1$, $\{p_1\}\,S\,\{q_1\}$ and $q_1 \to q$ infer $\{p\}\,S\,\{q\}$, where the implications are true in the structure.
- *Await*: from $\{p \wedge B\}\,T\,\{q\}$ infer $\{p\}\,\mathbf{await}\ B\ \mathbf{then}\ T\ \mathbf{end}\,\{q\}$.
- *Parallelism*: if $\{p_i\}\,S_i^\ast\,\{q_i\}$, $i = 1, \dots, n$, are locally correct proof outlines of the components and they are interference free, then $\{\bigwedge_i p_i\}\,[S_1 \parallel \dots \parallel S_n]\,\{\bigwedge_i q_i\}$.
- *Auxiliary variables*: from $\{p\}\,S\,\{q\}$ infer $\{p\}\,S_A\,\{q\}$, where $A$ is a set of auxiliary variables of $S$ and no variable of $A$ occurs free in $q$.

Proof outlines, their local correctness and interference freedom are those of [proof outlines and interference freedom](../proof-outlines-and-interference-freedom.md), under this translation: an assertion stands for the set of states satisfying it; an assignment $u := t$ is the basic action of its state transformer, and $\mathbf{skip}$ that of the identity; $\mathbf{await}\ B\ \mathbf{then}\ T\ \mathbf{end}$ is the atomic region with guard the set of states satisfying $B$ and body $T$; sequencing, conditionals and loops annotated with invariants are the corresponding annotated commands.

The auxiliary-variable rule may delete only variables that are auxiliary in the whole program $S$ of its premise, including all parallel components; the rule's side condition restricts only the postcondition $q$.

## Depends on

- [Auxiliary variables of a parallel program](auxiliary-variables-of-a-parallel-program.md)
- [Proof outlines and interference freedom](../proof-outlines-and-interference-freedom.md)

## Proof depends on

None.

## Expansion

This is the system for partial correctness. The total-correctness extension proposed with the original method, which adds a bound function to the loop rule and requires other components not to increase it, is unsound as first stated: the assertions in the proof of the bound's decrease are not tested for interference freedom. A development of total correctness must use one of the repaired formulations (keeping that proof in the outline, or requiring decrease along all syntactic paths) and is not covered here.

## Sources

- K. R. Apt and E.-R. Olderog, "Fifty years of Hoare's logic", *Formal Aspects of Computing* 31(6):751–807, 2019, <https://doi.org/10.1007/s00165-019-00501-3>, author version arXiv:1904.03917v1, <https://arxiv.org/abs/1904.03917v1>: Section 3.1 (the proof system for while programs), Section 8.1 (proof outlines, interference freedom, the PARALLELISM, AUXILIARY VARIABLES and AWAIT rules, and the termination problem found by Apt, de Boer and Olderog with its two repairs).
- S. Owicki and D. Gries, "An axiomatic proof technique for parallel programs I", *Acta Informatica* 6(4):319–340, 1976, <https://doi.org/10.1007/BF00268134>: not consulted; the original method as attributed by Apt and Olderog, Section 8.1.
- L. Prensa Nieto, "Completeness of the Owicki-Gries system for parameterized parallel programs", in *Proceedings 15th International Parallel and Distributed Processing Symposium (IPDPS 2001)*, workshop on Formal Methods for Parallel Programming: Theory and Applications, IEEE, 2001, pp. 1534–1541, <https://doi.org/10.1109/IPDPS.2001.925138>, author copy <https://www-sop.inria.fr/lemme/Leonor.Prensa/publications/Compl.ps.gz>: Section 1 (the parallel rule of the system it calls $\mathcal{O}$), Section 2.3 (proof outlines annotating every normal subprogram) and Section 3 (interference freedom condition (c)).
