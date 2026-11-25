# Cobar Coface App

Component formula for cofaces: extracted to avoid self-reference while
defining `cobarCoface`. The right endpoint `δ⁰` is the reusable recursive
iterated right coaction `rightCoactionPow G R n (L a)`. The left endpoint
`δ^{n+1}` is the left coaction. Interior cofaces use the public
reversed-position wrapper `cobarDeltaAtPos`, i.e. `deltaAtPos` with `Fin.rev`.
