# Well-typed programs can't be blamed

Let $t$ be a well-typed term of the [blame calculus](the-blame-calculus-and-its-subtyping-relations.md) with a subterm $\langle T \Leftarrow S \rangle^p\, s$ that contains the only
occurrences of the label $p$ in $t$.

- If $S <:^+ T$, then $t$ does not reduce to $\Uparrow p$.
- If $S <:^- T$, then $t$ does not reduce to $\Uparrow \bar p$.
- If $S <: T$, then $t$ reduces to neither $\Uparrow p$ nor $\Uparrow \bar p$.

Since $S <:^+ \mathrm{Dyn}$, a failing cast from typed code into a dynamically typed context is blamed on the context; since $\mathrm{Dyn} <:^- T$, a failing cast from
dynamically typed code into a typed context is blamed on the dynamically typed code. By [the factoring of naive subtyping](factoring-subtyping-into-positive-and-negative.md),
when a cast goes between a more precise and a less precise type, the less precisely typed side is blamed.

The proof shows that the property of being *safe for $p$* (every cast labeled $p$ is a positive subtyping, every cast labeled $\bar p$ a negative one, and every
subset test labeled $p$ succeeds) is preserved by reduction and that a term safe for $p$ does not step to $\Uparrow p$.

The corresponding result for the cast calculus of the gradually typed λ-calculus is [the blame-subtyping theorem for the GTLC](blame-subtyping-theorem-for-the-gtlc.md).

## Depends on

- [The blame calculus and its subtyping relations](the-blame-calculus-and-its-subtyping-relations.md)

## Proof depends on

- [Type safety of the blame calculus](type-safety-of-the-blame-calculus.md)
- [Factoring subtyping into positive and negative subtyping](factoring-subtyping-into-positive-and-negative.md)
- [Safe terms are preserved and are not blamed](safe-terms-are-preserved-and-not-blamed.md)

## Sources

- P. Wadler and R. B. Findler, "Well-typed programs can't be blamed", *Programming Languages and Systems, ESOP 2009*, LNCS 5502, Springer, pp. 1–16, 2009, <https://www.pure.ed.ac.uk/ws/portalfiles/portal/18384119/Wadler_Findler_2009_Well_Typed_Programs_Can_t_Be_Blamed.pdf>: Section 4, Figure 7 (safe terms), Propositions 9 and 10 (preservation and progress of safe terms), Corollary 1 and the discussion after it.
