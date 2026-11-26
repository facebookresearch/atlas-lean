# Refutational completeness of ordered resolution with selection

Let $\succ$ be an atom ordering and $\mathrm{sel}$ a selection function as in [ordered resolution with selection](ordered-resolution-with-selection.md), and let $N$ be a set of clauses without equality, over a signature with at least one constant symbol, that is saturated, $\mathrm{Res}^\succ_{\mathrm{sel}}(N) \subseteq N$. Then $N$ is unsatisfiable if and only if the empty clause $\bot$ belongs to $N$.

**Proof sketch.** On ground clauses, build a candidate Herbrand interpretation by induction over the clause ordering, as for unrestricted resolution, except that clauses with selected literals are never productive; a minimal counterexample would yield an inference whose conclusion is a smaller counterexample. Lift to general clauses: for a selection function on ground instances that selects, in each ground instance, the instances of the literals selected in a fixed clause of $N$ it comes from, the set $G_\Sigma(N)$ of ground instances is again saturated, so it has a Herbrand model, which is a model of $N$. Without a constant symbol $G_\Sigma(N)$ could be empty.

## Depends on

- [Ordered resolution with selection](ordered-resolution-with-selection.md)

## Proof depends on

- [Herbrand models suffice for clause sets](herbrand-models-suffice-for-clause-sets.md)
- [Ground instances of a saturated clause set are saturated](ground-instances-of-saturated-clause-sets-are-saturated.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 3.13, Lemma 3.40, Corollary 3.41 and Theorem 3.42 with its proof sketch, pp. 85–86.
