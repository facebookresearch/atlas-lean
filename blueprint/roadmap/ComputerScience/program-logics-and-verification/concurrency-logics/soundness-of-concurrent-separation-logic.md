# Soundness of concurrent separation logic

Consider a parallel heap-manipulating language with resource declarations, parallel composition $C_1 \parallel \dots \parallel C_n$ and
conditional critical regions $\mathbf{with}\ r\ \mathbf{when}\ B\ \mathbf{do}\ C$. Each resource $r$ is assigned a resource invariant $RI_r$,
and an assignment to a variable free in $RI_r$ may occur only inside a critical region for $r$. Besides the rules of
sequential separation logic, concurrent separation logic has

- the parallel rule: from $\{P_i\}\, C_i\, \{Q_i\}$ for $i = 1, \dots, n$ infer
  $\{P_1 \ast \dots \ast P_n\}\, C_1 \parallel \dots \parallel C_n\, \{Q_1 \ast \dots \ast Q_n\}$, provided no variable free in $P_i$ or $Q_i$ is changed in
  $C_j$ for $j \ne i$;
- the critical-region rule: from $\{(P \ast RI_r) \wedge B\}\, C\, \{Q \ast RI_r\}$ infer
  $\{P\}\, \mathbf{with}\ r\ \mathbf{when}\ B\ \mathbf{do}\ C\, \{Q\}$, provided no other process modifies variables free in $P$ or $Q$;
- the resource-declaration rule, which establishes $RI_{r_1} \ast \dots \ast RI_{r_m}$ from the initialization and reestablishes it on
  conclusion.

Call an assertion *precise* if for every state $(s, h)$ there is at most one subheap $h_0 \subseteq h$ with $s, h_0 \models P$.

**Theorem (Brookes).** If every resource invariant is precise, every triple derivable in this proof system, including
with the conjunction rule, is valid: any execution of the command from a state satisfying the precondition has no race
condition and no access to a dangling pointer, and every terminating execution ends in a state satisfying the
postcondition.

Precision is needed only because of the conjunction rule: Reynolds's counterexample uses the invariant
$RI_r = \mathrm{true}$ and the conjunction rule to derive $\{10 \mapsto -\}\, \mathbf{with}\ r\ \mathbf{when}\ \mathrm{true}\ \mathbf{do}\ \mathbf{skip}\, \{\mathrm{false}\}$, and in
the operational proof via step-indexed safety the conjunction rule is the only rule that requires precise invariants.

## Proof depends on

- [Step-indexed safety for concurrent separation logic](step-indexed-safety-for-concurrent-separation.md)

## Expansion

Fix the full sequential separation-logic rules, the resource-declaration rule and Brookes's trace semantics or the
operational semantics, so that validity and race freedom are stated for one concrete language.

## Sources

- P. W. O'Hearn, "Resources, concurrency, and local reasoning", *Theoretical Computer Science* 375(1–3):271–307, 2007: Section 2.4, Section 5 (proof rules) and Section 11 (Reynolds's counterexample, precise predicates, Brookes's soundness theorem).
- S. Brookes, "A semantics for concurrent separation logic", *Theoretical Computer Science* 375(1–3):227–270, 2007.
- X. Leroy, *Program logics*, fourth lecture, Collège de France, 2021, slide 48 (in the operational proof only the conjunction rule needs precise invariants).
