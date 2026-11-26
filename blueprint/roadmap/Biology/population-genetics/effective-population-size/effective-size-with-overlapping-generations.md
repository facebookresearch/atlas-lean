# Effective population size with overlapping generations

This node covers the effective size of populations with overlapping generations. In Moran's model of a
haploid population of $N \ge 2$ individuals ($N$ an integer), at each time step one individual, chosen
uniformly among the $N$ individuals present, dies and is replaced by the offspring of a parent chosen
uniformly among the same $N$ pre-event individuals, independently of the first choice and with
replacement (the dying individual may be the parent). The probability $h_t$ that two distinct
gene copies are not identical by descent satisfies $h_{t+1} = (1 - 2/N^2)\,h_t$; equating the decline
over one generation of $N$ steps with that of a haploid Wright–Fisher population gives an effective
size close to $N/2$ for large $N$. In general, overlapping generations change the effective size through
the variance of lifetime offspring number, and Hill (1972) expresses the effective size in terms of that
variance.

## Expansion

A sound expansion states the Moran computation exactly (the one-step recursion and the definition of
the generation length used to compare it with the Wright–Fisher model), and then, as separate pages,
the effective-size formulas of Felsenstein (1971) and Hill (1972) for an age-structured population,
each with the model and assumptions of its source.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 course text, University of Washington, version of December 2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section VI.8 "Other effects on effective population number", subsection "Overlapping
  generations", equations (VI-55)–(VI-57), pp. 273–274.
- J. Felsenstein, "Inbreeding and variance effective numbers in populations with overlapping
  generations", Genetics 68 (1971), 581–597, <https://doi.org/10.1093/genetics/68.4.581>.
- W. G. Hill, "Effective size of populations with overlapping generations", Theoretical Population
  Biology 3 (1972), 278–289, <https://doi.org/10.1016/0040-5809(72)90004-4>.
