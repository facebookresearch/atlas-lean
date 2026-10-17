---
article_id: af_1539c49795d4804f012a979a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Complex.NormalFamilies.vitali
---

# Vitali

Let `U` be open preconnected, `F` holomorphic on `U` and locally uniformly bounded, and `S ⊆ U`
accumulate at some `x₀ ∈ U`. If `Fₙ → g` pointwise on `S`, then `F` converges locally uniformly on
`U` to holomorphic `f` extending `g` on `S`. Source: Vitali convergence theorem, G. Vitali 1903;
see Hille, Analytic Function Theory Vol II and Conway II; Lean is open preconnected U locally
uniformly bounded with AccPt accumulation and pointwise limit on S extends to locally uniform
holomorphic convergence, Montel-related strengthening.
Proves `Wanted` entry `vitali`.

## Depends on

- [Is Locally Uniformly Bounded On](is-locally-uniformly-bounded-on.md)

## Proof depends on

- [Montel](montel.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Complex.NormalFamilies](../../../../../../../sources/v2/MathlibExt.md)
