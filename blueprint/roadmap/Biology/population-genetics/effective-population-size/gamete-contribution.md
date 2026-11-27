# Gamete contributions

Let `parent : Fin (2 * N) → Fin N` assign each of the $2N$ gene
copies of the offspring generation to the parent, among $N$ diploid parents, whose gamete it
comes from. The contribution of parent $i$ is the number
$n_i = \#\{c \mid \mathrm{parent}(c) = i\}$ of gene copies of the offspring generation that come
from it.
