# Is Solution

`x` solves the **replicator equation** `xᵢ' = xᵢ ((A x)ᵢ - ∑ⱼ xⱼ (A x)ⱼ)` on `[0, ∞)`,
coordinatewise. This is the condition of the library's replicator-equation predicate
`MathlibExt.Biology.Dynamics.Replicator.IsSolution` (in
`Domains.Biology.Dynamics.Replicator`) for the linear fitness `fun z => A *ᵥ z`, whose mean
fitness is `∑ⱼ xⱼ (A x)ⱼ`; it is restated here because `WantedExt` may not import `Domains`.
