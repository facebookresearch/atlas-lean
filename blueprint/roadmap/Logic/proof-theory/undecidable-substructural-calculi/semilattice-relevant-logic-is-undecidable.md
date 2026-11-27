# Urquhart's semilattice relevant logic is undecidable

The relevant logic $\mathsf{S}$ of all join-semilattice frames, introduced by Urquhart and widely expected to be decidable, is undecidable; consequently it lacks the finite model property.

**Theorem (Knudstorp).** The set $\mathsf{S}$ of formulas in $\{\wedge, \vee, \to\}$ valid in all [semilattice frames](positive-relevant-logics-and-routley-meyer-frames.md) $(S, \sqcup, 0)$ is undecidable.

**Corollary.** $\mathsf{S}$ does not have the finite model property: it differs from the set of formulas valid in all finite semilattice frames.

The corollary holds because $\mathsf{S}$ is recursively enumerable and the class of finite semilattices is recursively enumerable, so the finite model property would make $\mathsf{S}$ co-recursively enumerable as well, hence decidable.

## Depends on

- [Positive relevant logics and Routley–Meyer frames](positive-relevant-logics-and-routley-meyer-frames.md)
- [Recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Positive relevant logics between TWJ⁺ and the logic of finite sets are undecidable](positive-relevant-logics-above-twj-are.md)

## Expansion

$(\mathcal{P}_{\mathrm{fin}}(\mathbb{N}), \cup, \varnothing)$ is a semilattice frame, and every semilattice frame validates the frame conditions of $\mathsf{TWJ}^+$, so $\mathsf{TWJ}^+ \subseteq \mathsf{S} \subseteq \mathrm{Log}(\mathcal{P}_{\mathrm{fin}}(\mathbb{N}), \cup, \varnothing)$ and the general theorem applies. Urquhart's coordinatization method, which settles $\mathsf{R}$, $\mathsf{E}$ and $\mathsf{T}$, does not reach $\mathsf{S}$.

## Sources

- S. B. Knudstorp, "Undecidability in relevant logic", *The Journal of Symbolic Logic*, 2026, pp. 1–27, doi:10.1017/jsl.2026.10277; read as arXiv:2605.29880v2, <https://arxiv.org/abs/2605.29880v2>: Theorem 6.2 and Corollary 6.3 of arXiv:2605.29880v2.
