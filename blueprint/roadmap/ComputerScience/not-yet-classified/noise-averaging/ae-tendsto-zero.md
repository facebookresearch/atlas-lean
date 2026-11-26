# Tsitsiklis (1994), Lemma 1

On a probability space with a filtration `ℱ` indexed by `ℕ`,
let `W (t + 1) = (1 - α t) * W t + α t * w t` almost surely, where the step sizes `α t` and the
envelopes `B t` are `ℱ t`-measurable and the noise `w t` is `ℱ (t + 1)`-measurable. Suppose that
(a), (b) for every `t` the noise `w t` is conditionally centered given `ℱ t`, with conditional
second moment at most `max (B t) 0` (`IsCenteredNoise`), and that almost surely (c) `α t ∈ [0, 1]`
for every `t`, (d) `∑ t, α t = ∞`, (e) every partial sum of `α t ^ 2` is at most the
deterministic constant `C`, and the sequence `B t` is bounded above. Then `W t → 0` almost
surely, for any initial value `W 0`.
