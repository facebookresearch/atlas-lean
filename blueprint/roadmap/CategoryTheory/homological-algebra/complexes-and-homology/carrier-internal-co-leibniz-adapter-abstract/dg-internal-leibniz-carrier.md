# Dg Internal leibniz carrier

Abstract carrier internal Leibniz adapter: the internal differential
`Fi := HomComplex.Cochain.diff K` satisfies the carrier Leibniz shape
`(ofHom μ).comp Fi = (Fi ⊗ I).comp μ + (I ⊗ Fi).comp μ` against any
concat-shaped chain map `μ`, with the exact degree witnesses of hypothesis
`hFi` of `dgTotal_leibniz_combination` (`zero_add 1` on the multiply-first
side, `add_zero 1` on each differentiate-first leg).

Multiplication-shaped dual of `dgInternal_coLeibniz_carrier` (same proof
architecture, `comp` arguments dualized: the chain-map law runs `μ` before
`diff` instead of `D` after `diff`, and the additivity step is
`Cochain.add_comp` instead of `Cochain.comp_add`). The Cobar packager
instantiates `K := <cobar carrier>`, `μ := <carrier concat>`.
