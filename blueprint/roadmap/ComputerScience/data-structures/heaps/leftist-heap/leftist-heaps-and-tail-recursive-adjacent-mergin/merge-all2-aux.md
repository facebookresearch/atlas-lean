# Fuel-based merging of all heaps with tail-recursive passes

Over a linear order, merging all heaps of a list with a fuel $f \in \mathbb{N}$ is defined
recursively: the empty list gives the empty heap; a one-heap list $[t]$ gives $t$; a list of at
least two heaps gives the empty heap when the fuel is $0$, and with fuel $f + 1$ gives the result
with fuel $f$ on the list obtained by tail-recursive adjacent merging of the list with the empty
accumulator.

Merging all heaps of a list $L$ uses this with fuel equal to the length of $L$, which never runs
out because each pass shortens a list of at least two heaps.
