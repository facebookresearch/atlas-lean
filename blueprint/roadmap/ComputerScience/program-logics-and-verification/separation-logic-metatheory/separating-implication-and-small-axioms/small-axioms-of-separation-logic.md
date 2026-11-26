# Small axioms of separation logic

The heap language has the atomic commands $x := E$, $x := [E]$ (lookup), $[E] := F$ (mutation), $x := \mathrm{cons}(E_1, \dots, E_k)$ (allocation of $k$ consecutive fresh cells) and $\mathrm{dispose}(E)$; lookup, mutation and disposal fault at an unallocated address. The *small axioms*, where $x, m, n$ are distinct variables and $E \mapsto -$ abbreviates $\exists z.\, E \mapsto z$, are

- $\{E \mapsto -\}\ [E] := F\ \{E \mapsto F\}$;
- $\{E \mapsto -\}\ \mathrm{dispose}(E)\ \{\mathrm{emp}\}$;
- $\{x = m \wedge \mathrm{emp}\}\ x := \mathrm{cons}(E_1, \dots, E_k)\ \{x \mapsto E_1[m/x], \dots, E_k[m/x]\}$;
- $\{x = n \wedge \mathrm{emp}\}\ x := E\ \{x = E[n/x] \wedge \mathrm{emp}\}$;
- $\{E \mapsto n \wedge x = m\}\ x := [E]\ \{x = n \wedge E[m/x] \mapsto n\}$.

Each mentions only the cells its command accesses. The *structural rules* are the frame rule (from $\{P\}\, C\, \{Q\}$ infer $\{P \ast R\}\, C\, \{Q \ast R\}$ when no variable modified by $C$ is free in $R$), auxiliary variable elimination (from $\{P\}\, C\, \{Q\}$ infer $\{\exists x.\, P\}\, C\, \{\exists x.\, Q\}$ when $x$ is not free in $C$), variable substitution, and the rule of consequence. A command modifies only the variables it assigns, so mutation and disposal modify none.

## Depends on

- [Separating implication](separating-implication.md)

## Sources

- P. O'Hearn, J. Reynolds and H. Yang, "Local reasoning about programs that alter data structures", *Computer Science Logic (CSL 2001)*, LNCS 2142, Springer, 2001, pp. 1–19, <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/localreasoning.pdf>, Section 3 (the small axioms and the structural rules).
