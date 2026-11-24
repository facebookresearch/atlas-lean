# Each phase lengthens the shortest augmenting paths

Let $\mu$ be a valid partner array
and $c$ a natural number such that the first free round of $\mu$, if defined, is at least $c$.
For every natural number $f$, running at most $f$ Hopcroft–Karp phases from $\mu$, stopping
early when a phase finds no path, gives a valid partner array whose first free round, if
defined, is at least $c + f$.
