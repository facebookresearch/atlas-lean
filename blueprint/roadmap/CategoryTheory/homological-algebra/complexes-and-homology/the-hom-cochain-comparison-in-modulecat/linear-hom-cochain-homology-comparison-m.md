# Linear Hom Cochain Homology Comparison Module Cat

The canonical comparison from linear Hom-cochain cohomology to the
linear dual of homology, in `ModuleCat` with the canonical linear
structure `ModuleCat.instLinear` fixed.  Unlike the generic comparison
written directly at `ModuleCat R`, this term does not depend on instance
synthesis for `Linear R (ModuleCat R)` (which over `ℤ` selects
`Linear.preadditiveIntLinear`), so it composes with the `ModuleCat`
evaluation pairing for every `R`, including `ℤ`.
