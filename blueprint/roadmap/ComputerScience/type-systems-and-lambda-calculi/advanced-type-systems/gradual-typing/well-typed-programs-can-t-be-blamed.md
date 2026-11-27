# Well-typed programs can't be blamed

Let $t$ be a well-typed term of the [blame calculus](the-blame-calculus-and-its-subtyping-relations.md) with a cast $\langle T \Leftarrow S \rangle^p\, s$ such that neither $p$ nor $\bar p$ labels any other cast or subset test of $t$; in
particular $s$ contains neither label.

- If $S <:^+ T$, then $t$ does not reduce to $\Uparrow p$.
- If $S <:^- T$, then $t$ does not reduce to $\Uparrow \bar p$.
- If $S <: T$, then $t$ reduces to neither $\Uparrow p$ nor $\Uparrow \bar p$.

Since $S <:^+ \mathrm{Dyn}$, a failing cast from typed code into a dynamically typed context is blamed on the context; since $\mathrm{Dyn} <:^- T$, a failing cast from
dynamically typed code into a typed context is blamed on the dynamically typed code. By [the factoring of naive subtyping](factoring-subtyping-into-positive-and-negative.md),
when a cast goes between a more precise and a less precise type, the less precisely typed side is blamed.

The source states the hypothesis as "a subterm $\langle T \Leftarrow S \rangle^p\, s$ containing the only occurrences of $p$", which also admits occurrences inside $s$: with
$N = \{x : \mathrm{Int} \mid x \ge 0\}$, the term $\langle N \Leftarrow N \rangle^p\, (\langle N \Leftarrow \mathrm{Int} \rangle^p\, (-4))$ has $N <: N$ at its outer cast and still reduces to $\Uparrow p$, from the inner
subset test. The source proves the theorem by showing that the property of being *safe for $p$* (every cast labeled $p$ is a positive subtyping, every cast labeled
$\bar p$ a negative one, and every subset test labeled $p$ succeeds; its Figure 7) is preserved by reduction and that a term safe for $p$ does not step to $\Uparrow p$. As
printed, that relation is not preserved: it has no rule for the checked subset value $v_{\{x:B \mid t\}}$ that a successful test returns, it does not look inside the
predicates of the target types of casts, which the cast rule for subset types then exposes as tests, and after that rule its encoding of $\mathrm{let}$ requires an open
test to reduce to $\mathrm{true}$.

The corresponding result for the cast calculus of the gradually typed λ-calculus is [the blame-subtyping theorem for the GTLC](blame-subtyping-theorem-for-the-gtlc.md).

## Depends on

- [The blame calculus and its subtyping relations](the-blame-calculus-and-its-subtyping-relations.md)

## Proof depends on

- [Type safety of the blame calculus](type-safety-of-the-blame-calculus.md)
- [Factoring subtyping into positive and negative subtyping](factoring-subtyping-into-positive-and-negative.md)

## Expansion

This page becomes ready once:

- A safety invariant for the blame label that is preserved by reduction, covering checked subset values, the predicates in the target types of casts and the tests that are pending under a $\mathrm{let}$, with its progress property (proof prerequisite; not yet stated)

## Sources

- P. Wadler and R. B. Findler, "Well-typed programs can't be blamed", *Programming Languages and Systems, ESOP 2009*, LNCS 5502, Springer, pp. 1–16, 2009, <https://www.pure.ed.ac.uk/ws/portalfiles/portal/18384119/Wadler_Findler_2009_Well_Typed_Programs_Can_t_Be_Blamed.pdf>: Section 4, Figure 7 (safe terms), Propositions 9 and 10 (preservation and progress of safe terms), Corollary 1 and the discussion after it.
