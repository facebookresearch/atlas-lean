# Conditional law of a function of an independent pair

If `X` and `ε` are independent,
then conditionally on `X = x` the variable `g X ε` has law `(law ε).map (g x)`, for
`(law X)`-almost every `x`. This generalizes `MetaMathlibExt.condDistrib_add_of_indepFun`
(`MathlibExt/Probability/Distributions/GaussianConditioning.lean`), the additive case
`g x e = f x + e`, to an arbitrary jointly measurable `g`.
