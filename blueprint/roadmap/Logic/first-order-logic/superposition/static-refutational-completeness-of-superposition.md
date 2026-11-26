# Refutational completeness of superposition, static view

Let $N$ be a set of clauses over a signature with at least one constant symbol, as in the superposition calculus, that is [saturated up to redundancy](redundancy-and-fair-runs-for-superposition.md) with respect to the [superposition calculus](superposition-calculus.md). Then $N$ has a model if and only if $N$ does not contain the empty clause.

**Proof.** If $\bot \notin N$, then $T_\Sigma(\emptyset)/R_\infty$ is a model of $G_\Sigma(N)$ by the model construction theorem, and it is term-generated, hence a model of $N$. The constant is needed: $\{x \not\approx x\}$ over a signature with only a unary function symbol is saturated, since its only clause has no ground instance, so it is redundant and there is no inference from $N \setminus \mathrm{Red}(N)$ to check; yet $\{x \not\approx x\}$ has no model.

## Depends on

- [Redundancy and fair runs for superposition](redundancy-and-fair-runs-for-superposition.md)
- [Superposition calculus](superposition-calculus.md)

## Proof depends on

- [Model construction for superposition](superposition-model-construction.md)
- [Term-generated models of ground instances](term-generated-models-of-ground-instances.md)

## Sources

- U. Waldmann, *Automated Reasoning II*, lecture notes, Max Planck Institute for Informatics, summer semester 2024, <https://rg1-teaching.mpi-inf.mpg.de/autrea2-ss24/notes-current.pdf>, Section 3.4, Theorem 3.11 with its proof, p. 59.
