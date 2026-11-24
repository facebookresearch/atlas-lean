# The trivial-branch coefficient of the reduced map

In the setting of
`lyapunovSchmidt_patternBranch` (trivial branch, `φ ∈ ker L`, `ψ` vanishing on `range L`), assume
that along the trivial branch the linearization of `F` is affine in `d` with slope `L₁`:
`∂ₓF(0, d) = L + (d - d₀) L₁` for `d` near `d₀`. Then every factor `G` of the scalar bifurcation
function, `G̃(a, d) = a G(a, d)` near `(0, d₀)` with `G` strictly differentiable at `(0, d₀)`,
satisfies `G(0, d₀) = 0` and `∂_d G(0, d₀) = ψ(L₁ φ)`: these are the hypotheses `hG0` and (when
`ψ(L₁ φ) ≠ 0`) `htrans` of `lyapunovSchmidt_patternBranch`, now derived. Nothing is assumed
about `G(0, d)` for `d ≠ d₀`; `G` need not be continuous away from `(0, d₀)`.
