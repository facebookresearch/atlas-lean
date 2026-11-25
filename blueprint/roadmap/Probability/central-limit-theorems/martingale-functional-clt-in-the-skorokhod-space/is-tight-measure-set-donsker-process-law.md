# Tightness

Assume `∀ n, Measurable (X n)`, `iIndepFun X P`, `∀ i, IdentDistrib (X i) (X 0) P P`, `Integrable (X 0) P`, `MemLp (X 0) 2 P`, `P[X 0] = 0` and `IsBrownianReal B P'`.

**Tightness** of Donsker's polygonal laws on `C([0,1])`. This is a consequence of Donsker
convergence (`donsker_invariance_principle`) via Prokhorov's converse: the laws converge
weakly, so their closure in the space of laws is compact, hence the family is tight. It feeds
the tightness input of `tendstoInDistribution_skorokhod_of_tight_of_fdd` in
`tendstoInDistribution_skorokhodStepProcess`.

## Sources

- Billingsley (1999), Theorem 5.2 (Prokhorov, converse half) applied to Theorem 8.2.
