# Induced length distance

For points `x` and `y` of a pseudo-extended-metric space `X`,
`inducedLengthEdist x y ∈ [0, ∞]` is the infimum, over all continuous paths
`γ : [0, 1] → X` from `x` to `y`, of the length of `γ`, defined as its total
variation: the supremum over finite monotone sequences of parameters of the
sums of extended distances between consecutive points. It is `∞` when no
path joins `x` to `y`. For a subset `A ⊆ X`, applying the definition to `A`
with the restricted metric gives the length metric of `A`. This is the
induced length metric of Alexander, Kapovitch and Petrunin, *Alexandrov
geometry: foundations* (AMS GSM 236, 2024).
