# Type safety of the blame calculus

In the [blame calculus](the-blame-calculus-and-its-subtyping-relations.md):

- **Preservation.** If $\Gamma \vdash s : T$ and $s \longrightarrow t$, then $\Gamma \vdash t : T$.
- **Progress.** If $\vdash s : T$, then $s$ is a value, or $s \longrightarrow t$ for some term $t$, or $s \longrightarrow\ \Uparrow p$ for some blame label $p$.

Types are unique: $\Gamma \vdash s : S$ and $\Gamma \vdash s : T$ imply $S = T$.

## Depends on

- [The blame calculus and its subtyping relations](the-blame-calculus-and-its-subtyping-relations.md)

## Sources

- P. Wadler and R. B. Findler, "Well-typed programs can't be blamed", *Programming Languages and Systems, ESOP 2009*, LNCS 5502, Springer, pp. 1–16, 2009, <https://www.pure.ed.ac.uk/ws/portalfiles/portal/18384119/Wadler_Findler_2009_Well_Typed_Programs_Can_t_Be_Blamed.pdf>: Proposition 1 (unicity), Section 3.5, Lemmas 2–3 and Propositions 5 and 6 (preservation and progress).
