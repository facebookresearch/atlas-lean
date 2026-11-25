# Tensor δ v

Component-level Leibniz rule for the heterogeneous tensor product of
cochains: `δ` of `tensor f g` is `tensor (δ f) g` plus
`(-1) ^ m • tensor f (δ g)`, as maps out of `(tensorObj C₁ C₂).X r`.

Orientation follows the pinned `HomComplex.δ` (Conrad signs,
`HomComplex.δ_comp`): differentiating a composite differentiates the right
factor first, so the right/second-factor differential term carries `(-1) ^ m`
where `m` is the left degree. The tensor Koszul sign stays `(-1) ^ (n * i₁)` on the
`(i₁, i₂)`-summand, matching the pinned tensor-complex vertical sign
`(up ℤ).ε` on the second factor (`ComplexShape.ε_up_ℤ`).
