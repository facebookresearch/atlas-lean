# Null phenotypic covariance with relatedness

For a real `n × n` matrix `Φ` and real numbers `σ_g²` and `σ_e²`, with `n` a finite set of
individuals, the null covariance is

`Σ₀ = σ_g² Φ + σ_e² I`.

The inputs are arbitrary. When `Φ` is a positive semidefinite relationship matrix (for a pedigree,
twice the kinship) and `σ_g², σ_e² ≥ 0`, it is the phenotypic covariance of the polygenic mixed
model with relatedness under the null hypothesis: a polygenic effect with covariance `σ_g² Φ` plus
independent noise with covariance `σ_e² I`.
