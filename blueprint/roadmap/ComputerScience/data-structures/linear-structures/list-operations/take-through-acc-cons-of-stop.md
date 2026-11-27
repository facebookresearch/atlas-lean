# Accumulator-stopped prefix when the head update stops

Let $f$ be an update map, $\mathrm{stop}$ a test on accumulators, $c$ an accumulator, $x$ an
element and $L$ a list. If $\mathrm{stop}(f(c, x))$ is true, then the accumulator-stopped prefix
from $c$ of the list with head $x$ and tail $L$ is $[x]$.
