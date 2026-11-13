# Aep chebyshev

The asymptotic equipartition property, Chebyshev form: for the
self-information of a single sample from a finite law `p`, the probability
that its deviation from the entropy exceeds `ε` is at most the
self-information variance divided by `ε²`. This is the one-shot estimate
behind typical-set coding, using `selfInformationNatsZeroExtension`: values
off support are ignored by the probability weights.
