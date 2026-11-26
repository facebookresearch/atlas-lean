# The blame calculus and its subtyping relations

The blame calculus has types $S, T ::= B \mid S \to T \mid \mathrm{Dyn} \mid \{x : B \mid t\}$, with base types $B$, the dynamic type $\mathrm{Dyn}$ and subset (refinement)
types; ground types are $G ::= B \mid \mathrm{Dyn} \to \mathrm{Dyn}$. Terms include casts $\langle T \Leftarrow S \rangle^p\, s$ between compatible types $S \sim T$, where the blame
label $p$ has a complement $\bar p$ with $\bar{\bar p} = p$, and a failed cast reduces to blame $\Uparrow p$. Blaming $p$ (positive blame) means the term inside the cast
is at fault; blaming $\bar p$ (negative blame) means the context is. A cast between function types checks its argument with the labels swapped.

Four relations compare types:

- **Subtyping** $S <: T$: contravariant in function domains and covariant in ranges; a subset type is a subtype of its base; $S <: \{x : B \mid t\}$ when
  membership in $S$ entails $t$; and the only subtypes of $\mathrm{Dyn}$ are $\mathrm{Dyn}$ and the subtypes of ground types.
- **Positive subtyping** $S <:^+ T$ and **negative subtyping** $S <:^- T$, defined together and swapping roles in function domains, with $S <:^+ \mathrm{Dyn}$
  and $\mathrm{Dyn} <:^- T$ for all $S$, $T$, entailment checked only for $<:^+$, and $S <:^- T$ whenever $S <:^- G$ for a ground type $G$.
- **Naive subtyping** $S <:^n T$: covariant in both domain and range, so that it relates a more precise type to a less precise one.

All four are reflexive and transitive; $S <: T$, $S <:^+ T$ and $S <:^n T$ each imply $S \sim T$, but $S <:^- T$ does not. For example
$\mathrm{Int} \to \mathrm{Nat} <: \mathrm{Nat} \to \mathrm{Int}$ and $\mathrm{Nat} \to \mathrm{Nat} <:^n \mathrm{Int} \to \mathrm{Int}$, with $\mathrm{Nat} = \{x : \mathrm{Int} \mid x \ge 0\}$.

## Sources

- P. Wadler and R. B. Findler, "Well-typed programs can't be blamed", *Programming Languages and Systems, ESOP 2009*, LNCS 5502, Springer, pp. 1–16, 2009, <https://www.pure.ed.ac.uk/ws/portalfiles/portal/18384119/Wadler_Findler_2009_Well_Typed_Programs_Can_t_Be_Blamed.pdf>: Section 3 (types, casts, blame labels and reduction), Section 3.3 and Figure 5 (entailment and the four subtyping judgments), Propositions 3 and 4, and the examples after them.
