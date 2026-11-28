# Vertical Model

A proper birational model of `X × ℙ¹` with a vertical Cartier divisor, for the polarized
proper variety `(X, L)`: `L` is an ample line bundle (so `(Lⁿ) > 0`), the model polarization
`modelPolarization` (pulled-back `L^r` twisted by `𝒪(D)`) is a line bundle
(`modelPolarization_isLineBundle`), and the normalized intersection functionals are defined.

The central components are Gauss (`gauss`): each component valuation is the Gauss extension of
its restriction to `K(X)`, as for the components of a `𝔾ₘ`-equivariant model (BHJ, Lemma 4.7).
So distinct central components have distinct restrictions and `modelValue` is a function of the
base valuation; an arbitrary birational model need not have this property.
