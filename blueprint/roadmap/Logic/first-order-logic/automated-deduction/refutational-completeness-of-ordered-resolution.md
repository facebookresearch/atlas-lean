# Refutational completeness of ordered resolution with selection

Let $\succ$ be an atom ordering and $\mathrm{sel}$ a selection function as in [ordered resolution with selection](ordered-resolution-with-selection.md), and let $N$ be a set of clauses without equality that is saturated, $\mathrm{Res}^\succ_{\mathrm{sel}}(N) \subseteq N$. Then $N$ is unsatisfiable if and only if the empty clause $\bot$ belongs to $N$.

**Proof sketch.** On ground clauses, build a candidate Herbrand interpretation by induction over the clause ordering, as for unrestricted resolution, except that clauses with selected literals are never productive; a minimal counterexample would yield an inference whose conclusion is a smaller counterexample. Lift to general clauses with a lifting lemma for $\mathrm{Res}^\succ_{\mathrm{sel}}$, choosing a selection function on ground instances that selects the instances of the selected literals.

## Depends on

- [Ordered resolution with selection](ordered-resolution-with-selection.md)

## Proof depends on

- [Herbrand models suffice for clause sets](herbrand-models-suffice-for-clause-sets.md)
- [Lifting lemma for first-order resolution](lifting-lemma-for-first-order-resolution.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 3.13, Lemma 3.40, Corollary 3.41 and Theorem 3.42 with its proof sketch, pp. 85–86.
