# Lattice path of a parking preference

Let $\alpha = (a_1, \dots, a_n)$ be a sequence of
natural numbers. Its lattice path is the sequence of $2n$ steps, each an Up step $(1, 1)$ or a
Down step $(1, -1)$, obtained by taking, for each spot $s = 1, \dots, n$ in turn, one Up step
for every index $i$ with $a_i = s$ followed by one Down step, and then appending Down steps
until there are $2n$ steps. When every $a_i$ lies in $\{1, \dots, n\}$ this gives exactly $2n$
steps and nothing is appended; if moreover $\alpha$ is weakly increasing, the $i$-th Up step is
preceded by exactly $a_i - 1$ Down steps.

## Sources

- J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez, *Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024), Article A44, Section 3 (Remark 3.3).
