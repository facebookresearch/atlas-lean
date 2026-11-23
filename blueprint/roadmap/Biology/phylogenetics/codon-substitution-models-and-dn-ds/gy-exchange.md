# Goldman–Yang codon exchangeability

Let $I$ be a set of codon states with labels $\nu : I \to$ [codons](codon.md) and an amino-acid map $\mathrm{aa}$ on $I$, and let $\kappa, \omega$ be real. The Goldman–Yang exchangeability of $i, j \in I$ is

$$s_{ij} = \begin{cases} k_{ij} \cdot a_{ij} & \text{if } \nu(i), \nu(j) \text{ form a single change},\\ 0 & \text{otherwise,}\end{cases}$$

where $k_{ij} = \kappa$ if the change [consists of transitions](is-transition-change.md) and $1$ otherwise, and $a_{ij} = 1$ if $\mathrm{aa}(i) = \mathrm{aa}(j)$ and $\omega$ otherwise.
