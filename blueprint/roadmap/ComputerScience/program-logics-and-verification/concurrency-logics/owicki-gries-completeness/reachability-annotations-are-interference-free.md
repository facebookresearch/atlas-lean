# Reachability annotations give interference-free proof outlines

For a valid triple about a parallel program, add a history variable recording every atomic action, and annotate each control point of each component with the set of states reachable there. These annotations form locally correct, interference-free proof outlines whose pre- and postconditions match the triple.

Use the programs, [auxiliary variables](auxiliary-variables-of-a-parallel-program.md) and the proof outlines and interference freedom of the [Owicki–Gries proof system](owicki-gries-system-with-auxiliary-variables.md), with assertions taken semantically as sets of states. As in the source, program variables range over $\mathbb{N}$; a finite sequence $a_1, \dots, a_k$ is coded by a natural number $\lceil a_1, \dots, a_k \rceil$, with $\lceil\,\rceil$ the empty sequence and $a \frown c$ the code of $a$ extended by $c$, both computable.

Let $S = [S_1 \parallel \dots \parallel S_n]$, let $p$ and $q$ be sets of states of $S$, and let $z$ be a variable not occurring in $S$; states of the instrumented program extend states of $S$ by a value of $z$, and $p$, $q$ are read on the $S$-part. Let $\bar x$ denote the code of the current values of the variables of $S$. The *history instrumentation* $S_i^\ast$ of $S_i$ replaces

- every $\mathbf{await}\ B\ \mathbf{then}\ R\ \mathbf{end}$ with $R \ne \mathbf{skip}$ by $\mathbf{await}\ B\ \mathbf{then}\ z := z \frown \lceil i, \bar x \rceil; R\ \mathbf{end}$, and
- every assignment $y := t$ outside $\mathbf{await}$ bodies by $\langle z := z \frown \lceil i, \bar x \rceil; y := t \rangle$.

Then $\{z\}$ is a set of auxiliary variables of $S^\ast = z := \lceil\,\rceil; [S_1^\ast \parallel \dots \parallel S_n^\ast]$. Deleting the assignments to $z$ leaves each original assignment $y := t$ as $\langle y := t \rangle$; the source, in which single assignments are executed atomically, takes this deletion to give back $S$. For each component $i$ and each subprogram $T$ of $S_i^\ast$ not inside an atomic region, let $r_{T,i}$ be the set of states $s^\ast$ of $S^\ast$ such that some computation of $S^\ast$ from a state satisfying $p$ reaches a configuration in which component $i$ is about to execute $T$ and the state is $s^\ast$; let $r_{\mathrm{end},i}$ be the set of states reached by such computations once component $i$ has terminated. Annotating $S_i^\ast$ with $\mathrm{pre}(T) = r_{T,i}$ and postcondition $r_{\mathrm{end},i}$ gives the annotated program $A(S_i^\ast)$.

The lemma below is quoted as Prensa Nieto states it and attributes it to the completeness proofs of Owicki and of Apt; she does not prove it.

**Lemma.** If $\{p\}\,S\,\{q\}$ is valid in the sense of partial correctness, then

1. every state $s$ satisfying $p$ gives a state $s^\ast$ with $z = \lceil\,\rceil$ in $\bigcap_i \mathrm{pre}(A(S_i^\ast))$;
2. each $A(S_i^\ast)$ is a locally correct proof outline;
3. the outlines $A(S_1^\ast), \dots, A(S_n^\ast)$ are interference free; and
4. every state in $\bigcap_i r_{\mathrm{end},i}$ has its $S$-part in $q$.

In the source's words, the auxiliary variable records the progress of the computation in the other processes, allowing the effects of parallel execution to be expressed; a history variable is used rather than program counters because Boolean evaluations cannot update auxiliary variables atomically.

## Depends on

- [Auxiliary variables of a parallel program](auxiliary-variables-of-a-parallel-program.md)
- [Owicki–Gries proof system with auxiliary variables](owicki-gries-system-with-auxiliary-variables.md)

## Proof depends on

- [Auxiliary variables of a parallel program](auxiliary-variables-of-a-parallel-program.md)
- [Owicki–Gries proof system with auxiliary variables](owicki-gries-system-with-auxiliary-variables.md)

## Expansion

The source refers to the completeness proofs of Owicki and of Apt for the construction of these annotations and for the proof of the four conditions for a fixed number of components. A development needs the interleaving semantics of parallel programs with $\mathbf{await}$, the notion of the control point of a component at which an annotation is placed, and proofs of conditions 1–4.

## Sources

- L. Prensa Nieto, "Completeness of the Owicki-Gries system for parameterized parallel programs", in *Proceedings 15th International Parallel and Distributed Processing Symposium (IPDPS 2001)*, workshop on Formal Methods for Parallel Programming: Theory and Applications, IEEE, 2001, pp. 1534–1541, <https://doi.org/10.1109/IPDPS.2001.925138>, author copy <https://www-sop.inria.fr/lemme/Leonor.Prensa/publications/Compl.ps.gz>: Section 2.2 (natural-number states and sequence codes), Section 3 (history variable instead of program counters, conditions (a)–(d)), Section 3.1 (the program extension) and Section 3.2 (the reachable-state annotations of the completeness proofs of Owicki and of Apt).
- S. Owicki, "A consistent and complete deductive system for the verification of parallel programs", in *Proceedings of the Eighth Annual ACM Symposium on Theory of Computing (STOC '76)*, ACM, 1976, pp. 73–86, <https://doi.org/10.1145/800113.803634>: not consulted; attributed by Prensa Nieto, Sections 3 and 3.2.
- K. R. Apt, "Recursive assertions and parallel programs", *Acta Informatica* 15(3):219–232, 1981, <https://doi.org/10.1007/BF00289262>: not consulted; attributed by Prensa Nieto, Section 3.2 and footnote 6.
