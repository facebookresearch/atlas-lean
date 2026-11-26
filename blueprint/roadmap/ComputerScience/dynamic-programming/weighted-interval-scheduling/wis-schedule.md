# Weighted interval scheduling algorithm

For intervals $1, \dots, n$ with start times $s$,
finish times $f$ and weights $w$, the algorithm sorts $1, \dots, n$ by finish time with merge sort,
charging one unit per comparison of two finish times, into the order
$\sigma(1), \dots, \sigma(n)$. It then builds the bottom-up table $(M, P)$ for the intervals with
start times $s \circ \sigma$, finish times $f \circ \sigma$ and weights $w \circ \sigma$, traces
back through it from $n$, and returns $M_n$ together with the image under $\sigma$ of the
traced-back set.
