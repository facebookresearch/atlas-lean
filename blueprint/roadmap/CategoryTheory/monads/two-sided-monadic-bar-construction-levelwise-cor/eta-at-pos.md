# Eta At Pos

Raw left-counted unit insertion `T ^ n ⟶ T ^ (n + 1)`: position `0` is the
innermost (left-module end) factor and successors recurse under `T`. Public bar
degeneracies use the right-counted wrapper `barEtaAtPos n i = etaAtPos n i.rev`.
