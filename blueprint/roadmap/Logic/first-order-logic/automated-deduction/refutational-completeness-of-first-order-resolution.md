# Refutational completeness of first-order resolution

Let $N$ be a set of first-order clauses without built-in equality. An uninterpreted predicate symbol that happens to be named like equality is allowed, with no equality axioms assumed. Let $\mathrm{Res}^*(N)$ be the closure of $N$ under binary resolution with most general unifiers and factoring.

1. If $\mathrm{Res}(N) \subseteq N$, that is, $N$ is saturated, then $N$ is unsatisfiable if and only if $\bot \in N$.
2. Consequently, an arbitrary $N$ is unsatisfiable if and only if the empty clause $\bot$ is derivable from $N$ by resolution and factoring. Then a finite derivation exists.

**Proof.** For part 1, saturation of $N$ makes the set $G_\Sigma(N)$ of ground instances saturated under propositional resolution, by the [lifting lemma](lifting-lemma-for-first-order-resolution.md). By [Herbrand's theorem](herbrand-models-suffice-for-clause-sets.md) and its lemmas, $N$ is unsatisfiable exactly when $G_\Sigma(N)$ is. Since propositional resolution is sound and complete, this happens exactly when $\bot \in G_\Sigma(N)$, that is, $\bot \in N$.

For part 2, apply part 1 to $\mathrm{Res}^*(N)$. It is equisatisfiable with $N$ by [soundness](soundness-of-first-order-binary-resolution-and.md), and every element of it has a finite derivation.

## Depends on

- [Soundness of first-order binary resolution and factoring](soundness-of-first-order-binary-resolution-and.md)

## Proof depends on

- [Lifting lemma for first-order resolution](lifting-lemma-for-first-order-resolution.md)
- [Herbrand models suffice for clause sets](herbrand-models-suffice-for-clause-sets.md)

## Sources

- *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, summer semester 2008, lecture 10, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ss08/script/lecture10.pdf>: Theorem 3.39 (refutational completeness of general resolution for saturated sets) with its proof, and Theorem 3.40 (compactness of first-order logic, derived from it).
