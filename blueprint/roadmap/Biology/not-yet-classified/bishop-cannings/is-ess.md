# Is ESS

`p` is an **evolutionarily stable strategy** of the matrix game `A` (Maynard Smith): `p` is
mixed and for every mixed `q ≠ p`, either `qᵀ A p < pᵀ A p`, or `qᵀ A p = pᵀ A p` and
`qᵀ A q < pᵀ A q`. This is definitionally the library's predicate
`MathlibExt.Biology.Dynamics.Replicator.IsESS` (in `Domains.Biology.Dynamics.ReplicatorStability`),
restated here because `WantedExt` may not import `Domains`.
