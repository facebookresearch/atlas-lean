# The SKAT-O kernel of a genotype matrix, variant weights and ρ

For a real `n × m` genotype matrix `G`, variant weights `a ∈ ℝᵐ` and a real number `ρ`, the SKAT-O
kernel is the `n × n` matrix

`K_ρ = G diag(a) R_ρ diag(a) Gᵀ`

(Lee, Wu and Lin 2012, §2), where `R_ρ = (1 - ρ) I + ρ 𝟙 𝟙ᵀ` is the [SKAT-O matrix](skat-ocorr.md)
with unit diagonal and off-diagonal entries `ρ`. Any real `ρ` and weights are allowed. It equals
`(1 - ρ) G diag(a²) Gᵀ + ρ (G a)(G a)ᵀ` ([decomposition](skat-okernel-eq.md)).
