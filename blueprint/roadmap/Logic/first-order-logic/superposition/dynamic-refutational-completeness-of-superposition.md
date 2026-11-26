# Refutational completeness of superposition, dynamic view

Let $N_0 \vdash N_1 \vdash \cdots$ be a [fair run](redundancy-and-fair-runs-for-superposition.md) of the superposition calculus, over a signature with at least one constant symbol, with limit $N_\infty$. Then $N_0$ has a model if and only if the empty clause does not belong to $N_\infty$.

**Proof.** If $\bot \notin N_\infty$, then $N_\infty$ is saturated up to redundancy and has a term-generated model; every clause of $N_0$ lies in $N_\infty$ or is redundant with respect to it, so this model satisfies $G_\Sigma(N_0)$ and hence $N_0$. Conversely $N_0 \models N_\infty$.

## Depends on

- [Redundancy and fair runs for superposition](redundancy-and-fair-runs-for-superposition.md)

## Proof depends on

- [Fair superposition runs saturate up to redundancy](fair-runs-saturate-up-to-redundancy.md)
- [Refutational completeness of superposition, static view](static-refutational-completeness-of-superposition.md)
- [Term-generated models of ground instances](term-generated-models-of-ground-instances.md)

## Sources

- U. Waldmann, *Automated Reasoning II*, lecture notes, Max Planck Institute for Informatics, summer semester 2024, <https://rg1-teaching.mpi-inf.mpg.de/autrea2-ss24/notes-current.pdf>, Section 3.4, Theorem 3.17 with its proof, p. 61.
