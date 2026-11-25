# For C i > 0 plant trajectories are exactly the zone-equation solutions

Let `ι` be a finite index set of zones with decidable equality, with capacities `C i`, inter-zone
conductances `G i j` and boundary conductances `g0 i`. Let `C i > 0` for every `i`, and let `T i`,
`Tout` and `P i` be real functions of time. The curve `s ↦ (T i(s))_i` satisfies, at every time `t`,

`d/dt (T i(t))_i = A (T i(t))_i + B (Tout(t), P(t))`,

with the [state matrix](thermal-a.md) `A` and the [input matrix](thermal-b.md) `B`, if and only if
at every time `t` and in every zone `i`, `T i` has a derivative `T i′(t)` with

`C i T i′(t) = ∑_j G i j (T j(t) - T i(t)) + g0 i (Tout(t) - T i(t)) + P i(t)`.

No continuity of `Tout` or `P` is assumed. In the physical reading `G i j = G j i ≥ 0` and
`g0 i ≥ 0`; the equivalence holds for all real `G` and `g0`.
