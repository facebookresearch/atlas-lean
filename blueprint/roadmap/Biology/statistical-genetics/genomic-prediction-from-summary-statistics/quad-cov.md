# Training integral of the target cross moment of two scores

Let `μ` be a measure on a measurable space `Ω` (the training randomness), let `S` be a real `M × M`
matrix (the target LD matrix), and let `a = (a_1, …, a_M)` and `b = (b_1, …, b_M)` be real functions
on `Ω` (random effect vectors). Define

`C_S(a, b) = ∫ ∑_j ∑_k a_j S_jk b_k dμ = ∫ aᵀ S b dμ`.

The integral of a non-integrable function is taken to be `0`; the integrand is integrable when every
`a_j` and `b_k` is square integrable. For fixed effect vectors, `aᵀ S b` is the cross moment of the
scores `xᵀ a` and `xᵀ b` in a target population whose genotypes `x` have raw second moments `S`
([cross moment of a target phenotype with a polygenic score](integral-pheno-mul-score.md));
`C_S(a, b)` integrates it over training, which is an expectation when `μ` is a probability measure.
For true effects `β` and estimated effects `β̂`, `C_S(β, β̂)`, `C_S(β, β)` and `C_S(β̂, β̂)` are
called the cross term, the genetic-value term and the score term.
