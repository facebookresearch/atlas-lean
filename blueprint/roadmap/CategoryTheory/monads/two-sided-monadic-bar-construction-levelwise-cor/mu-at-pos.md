# Mu At Pos

Raw left-counted multiplication `T ^ (n + 1) ⟶ T ^ n`: position `0` is the
innermost (left-module end) factor and successors recurse under `T`. Public bar
faces use the right-counted wrapper `barMuAtPos n i = muAtPos n i.rev`.
