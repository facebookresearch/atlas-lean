# Positive relevant logics between TWJ⁺ and the logic of finite sets are undecidable

Every set of positive formulas that contains the relevant logic $\mathsf{TWJ}^+$ and is contained in the logic of the semilattice of finite sets of naturals under union is undecidable. This covers $\mathsf{R}^+$, $\mathsf{E}^+$, $\mathsf{T}^+$ and Urquhart's semilattice logic.

**Theorem (Knudstorp).** Let $\mathsf{L}$ be any set of formulas in the language $\{\wedge, \vee, \to\}$ of [positive relevant logic](positive-relevant-logics-and-routley-meyer-frames.md) with

$$
\mathsf{TWJ}^+ \subseteq \mathsf{L} \subseteq \mathrm{Log}(\mathcal{P}_{\mathrm{fin}}(\mathbb{N}), \cup, \varnothing).
$$

Then $\mathsf{L}$ is undecidable. No closure condition on $\mathsf{L}$ is required. In particular $\mathsf{TWJ}^+$, $\mathsf{C}^+$, $\mathsf{T}^+$, $\mathsf{E}^+$, $\mathsf{R}^+$ and $\mathsf{SetFr}$ are undecidable (Theorem 6.4 of the source).

The source notes that the upper bound may equally be taken to be the logic of the frame $(\mathbb{N}^2, \cdot, (0, 0))$. Since each of the named logics is recursively enumerable and so is its class of finite frames, none of them has the finite model property.

## Depends on

- [Positive relevant logics and Routley–Meyer frames](positive-relevant-logics-and-routley-meyer-frames.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

For each finite set $\mathcal{W}$ of Wang tiles the proof builds a formula $\psi_\mathcal{W}$ with $\psi_\mathcal{W} \notin \mathsf{L}$ iff $\mathcal{W}$ tiles $\mathbb{Z}^2$. If $\psi_\mathcal{W} \notin \mathsf{TWJ}^+$, a refuting frame satisfies the conditions corresponding to hypothetical syllogism, prefixing and suffixing, and these force tilings of arbitrarily large finite isosceles right triangular regions $\mathbb{O}(k)$ of the plane, so $\mathcal{W}$ tiles $\mathbb{Z}^2$. Conversely, a tiling of $\mathbb{Z}^2$ yields a valuation on $(\mathcal{P}_{\mathrm{fin}}(\mathbb{N}), \cup, \varnothing)$ refuting $\psi_\mathcal{W}$. Thus the tiling problem reduces to the complement of membership in $\mathsf{L}$. This gives a new proof of Urquhart's undecidability of $\mathsf{T}^+$, $\mathsf{E}^+$ and $\mathsf{R}^+$, which went through von Neumann's coordinatization of projective geometries.

## Sources

- S. B. Knudstorp, "Undecidability in relevant logic", *The Journal of Symbolic Logic*, 2026, pp. 1–27, doi:10.1017/jsl.2026.10277; read as arXiv:2605.29880v2, <https://arxiv.org/abs/2605.29880v2>: Theorems 6.1 and 6.4 of arXiv:2605.29880v2 and the proof of Theorem 6.1, with the tiling lemmas of Section 5.
