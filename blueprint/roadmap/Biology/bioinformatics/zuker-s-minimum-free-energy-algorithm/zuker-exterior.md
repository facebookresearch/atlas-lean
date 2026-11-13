# Zuker exterior-loop recursion

The exterior-loop recursion on the prefix `[0, len)`: `W(0) = 0` and
`W(len + 1) = min (W(len), min_{i ≤ len} W(i) + V(i, len + 1 - i))` (the last base is unpaired,
or closes an exterior branch `(i, len)`).
