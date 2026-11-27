# Every introduction grows at rate `R₀` under irreducibility

Let `μ` be a σ-finite measure on `Ω` and `K` a [positive](is-positive.md), compact,
[ideal-irreducible](is-ideal-irreducible.md) operator on `L¹(Ω, μ)` whose
[basic reproduction ratio](generation-growth.md) `R₀ = r(K)` is positive. Then every nonzero
nonnegative infective distribution `φ ∈ L¹(Ω, μ)` grows at exactly the rate `R₀`:
`‖K^m φ‖^(1/m) → R₀` as `m → ∞`. In particular, when `R₀ > 1`, every such introduction has
unbounded generation sizes `‖K^m φ‖`.

The source does not state this; it is a corollary of the setting it describes. Diekmann,
Heesterbeek and Metz write the long run as `K^m φ ~ c(φ) R₀^m φ_d`, with `c(φ) > 0` for
nonnegative nonzero `φ`, under conditions on `K` (their Eq. (2.3)), and remark that an
irreducibility hypothesis is needed for every introduction of infectivity to lead to an epidemic
when `R₀ > 1` (their Remark 3). The proof uses a
[strictly positive eigenfunctional](strictly-positive-eigenfunctional-of-an-irreduci.md) `ψ` of
the adjoint of `K` for `R₀`: from `∫ ψ (K^m φ) dμ = R₀^m ∫ ψ φ dμ` and `∫ ψ φ dμ > 0` it follows
that `‖K^m φ‖ ≥ R₀^m (∫ ψ φ dμ) / ‖ψ‖_∞`, while `‖K^m φ‖ ≤ ‖K^m‖ ‖φ‖` and
`‖K^m‖^(1/m) → R₀`.

## Depends on

- [The basic reproduction ratio `R₀`](generation-growth.md)
- [Is Positive](is-positive.md)
- [Is Ideal Irreducible](is-ideal-irreducible.md)

## Proof depends on

- [Strictly positive eigenfunctional of an irreducible compact positive operator](strictly-positive-eigenfunctional-of-an-irreduci.md)

## Sources

- O. Diekmann, J. A. P. Heesterbeek and J. A. J. Metz, "On the definition and the computation of
  the basic reproduction ratio R₀ in models for infectious diseases in heterogeneous populations",
  J. Math. Biol. 28 (1990) 365–382, Eq. (2.3) (p. 368) and Remark 3 (p. 369).
