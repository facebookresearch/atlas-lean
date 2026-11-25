# Within- and between-individual non-identity under full-sib mating

At a single autosomal locus, let $h_t$ be the common probability of non-identity by descent
of the two copies within either individual, and $k_t$ the probability for independently
drawn copies from the two siblings. For fair independent Mendelian transmissions without
selection, the pair starts at $(h_0,k_0)$ and updates by

$$(h_{t+1}, k_{t+1}) = (k_t,\; h_t/4 + k_t/2).$$

The two copies within an offspring always come from different parents. For copies drawn
from two siblings, the parental origins differ half of the time. Of the same-parent draws,
half trace to distinct copies of that parent, with non-identity probability $h_t$; the rest
trace to the same copy and are identical by descent.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics*, December 2019, §V.10, [pp. 234–235](https://felsenst.github.io/pgbook/pgbook.pdf), equations (V-26) and (V-27).
