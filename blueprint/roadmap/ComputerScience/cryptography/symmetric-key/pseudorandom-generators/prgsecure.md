# Asymptotic PRG security relative to `Admissible`

**Asymptotic PRG security relative to `Admissible`** of a family `G n : S n → Y n`: the
family expands (`PRGExpanding`) and is indistinguishable from uniform against every admissible
family of distinguishers (`PRGIndistinguishable`).

This is the part of Katz and Lindell, Definition 3.14, expressible without a complexity model,
not the definition verbatim. Omitted source conditions: `G` deterministic polynomial-time
computable, output length `ℓ(n)` polynomial, distinguishers probabilistic polynomial-time. The
first two are not imposed, so a noncomputable family can satisfy `PRGSecure`; the third must be
supplied through `Admissible`.
