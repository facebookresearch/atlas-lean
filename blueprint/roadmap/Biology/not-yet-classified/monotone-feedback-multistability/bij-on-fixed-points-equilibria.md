# Equilibria of the positive feedback loop

**Equilibria of the positive feedback loop** (Angeli–Sontag 2004, Theorem 3, first part). Let
`sys` be a single-input single-output system (positivity cone `K`, state space `X` equal to the
closure of its interior, `C¹` vector field `f` and output map `h`, and a solution map `φ` giving,
for every `ξ ∈ X` and every input `u`, the unique solution from `ξ` on `[0, ∞)` that stays in `X`)
that is monotone, with a non-degenerate input-to-state characteristic `kX` on `U` (each constant
input `u ∈ U` has the unique globally asymptotically stable equilibrium `kX u ∈ X`, with
`det D_x f(kX u, u) ≠ 0`), and assume `h(X) ⊆ U`. Then `u ↦ kX u` is a bijection from the fixed
points `u ∈ U` of the input/output characteristic `kY = h ∘ kX` onto the equilibria `x ∈ X` of the
closed loop `ẋ = f(x, h(x))`.

## Sources

- D. Angeli, E. D. Sontag, Systems Control Lett. 51 (2004) 185–202, Theorem 3 (arXiv:q-bio/0309002).
