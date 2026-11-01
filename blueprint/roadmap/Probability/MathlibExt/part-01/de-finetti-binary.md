---
article_id: af_1870c1dc623522d6ebd88752
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Probability.DeFinettiWanted.deFinetti_binary
---

# De Finetti

If `μ : ProbabilityMeasure (ℕ → Bool)` is invariant under every finitely supported permutation of
`ℕ`, then there exists a mixing measure `ν : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)` such that for
all disjoint `A B : Finset ℕ` the cylinder probability equals `ENNReal.ofReal (∫ p ^ |A| * (1-p) ^
|B| ∂ν)`. Source: B. de Finetti, Funzione caratteristica di un fenomeno aleatorio, Atti Accad.
Naz. Lincei 4 (1931) and La prévision: ses lois logiques (1937); textbook in Kallenberg,
Probabilistic Symmetries and Invariance Principles; also Durrett, Probability Theory and Examples

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Probability.DeFinetti](../../../../sources/v2/MathlibExt.md)
