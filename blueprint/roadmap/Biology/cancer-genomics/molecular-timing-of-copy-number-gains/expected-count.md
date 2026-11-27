# Expected number of mutations of a given multiplicity

For a [gain history](gain-history.md) with descendant counts $\delta_i$ and final copy number $c_1$, a per-copy mutation rate $\mu$, an event time $t$ and a natural number $m$, the expected number of mutations of multiplicity $m$ is

$$E_m = \mu t\, \#\{i : \delta_i = m\} + [m = 1]\, \mu c_1 (1 - t),$$

where $[m = 1]$ is $1$ if $m = 1$ and $0$ otherwise: mutations acquired on copy $i$ before the event have multiplicity $\delta_i$, those acquired after it multiplicity $1$ (Purdom et al. 2013; Gerstung et al. 2020).

## Sources

- E. Purdom, C. Ho, C. S. Grasso, M. J. Quist, R. J. Cho, P. Spellman, *Methods and challenges in timing chromosomal abnormalities within cancer samples*, Bioinformatics 29 (2013), 3113–3120.
- M. Gerstung et al., *The evolutionary history of 2,658 cancers*, Nature 578 (2020), 122–128.
