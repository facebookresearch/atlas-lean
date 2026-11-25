# CBC unchaining inverts chaining

Let `X` be an additive group and `pinv` a left inverse of `p`, that is `pinv
(p x) = x` for every `x`. For every length `n`, initial value `iv` and message
`m : Fin n → X`, unchaining the CBC chain of `m` with `pinv` recovers `m`.
