# Accumulator-stopped inclusive prefix of a list

Let $f$ be an update map taking an accumulator $c$ and an element $x$ to a new accumulator
$f(c, x)$, and let $\mathrm{stop}$ be a test that is true or false on accumulators. The
accumulator-stopped prefix of a list from an accumulator $c$ is defined recursively. For the empty
list it is the empty list. For a list with head $x$ and tail $L$, let $c' = f(c, x)$: if
$\mathrm{stop}(c')$ is true, the result is $[x]$; otherwise it is $x$ followed by the
accumulator-stopped prefix of $L$ from $c'$.

So the prefix runs through the first element after whose update the accumulator satisfies
$\mathrm{stop}$, including that element; the initial accumulator is not tested, and if no updated
accumulator satisfies $\mathrm{stop}$ the result is the whole list.
