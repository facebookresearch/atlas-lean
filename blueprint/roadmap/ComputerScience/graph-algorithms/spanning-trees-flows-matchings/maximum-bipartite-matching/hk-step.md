# Hopcroft–Karp step

Given a partner array $\mu$, consider the phase of $\mu$, a list of
paths, each a list of pairs. If the phase is empty, the step returns nothing; otherwise it returns
the flip of $\mu$ along the concatenation of all the paths of the phase.
