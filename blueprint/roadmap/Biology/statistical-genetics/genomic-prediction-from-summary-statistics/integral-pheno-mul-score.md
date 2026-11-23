# Cross moment of a target phenotype with a polygenic score

Let `ν` be a measure on a measurable space `Ξ` (the target population), let `x_1, …, x_M`
(genotypes) and `e` (noise) be real functions on `Ξ` that are square integrable with respect to `ν`,
and let `S` be a real `M × M` matrix with `∫ x_j x_k dν = S_jk` for all `j, k` (the raw second
moments of the genotypes). If `∫ e x_k dν = 0` for every `k`, then for all `a, b ∈ ℝ^M` the
phenotype `y = ∑_j a_j x_j + e` satisfies

`∫ y (∑_k b_k x_k) dν = ∑_j ∑_k a_j S_jk b_k = aᵀ S b`.

With `e = 0` this is the cross moment of the scores `xᵀ a` and `xᵀ b`. When `ν` is a probability
measure and the genotypes have mean zero, these cross moments are covariances, so the phenotype and
the genetic value `xᵀ a` have the same covariance `aᵀ S b` with every score `xᵀ b`.
