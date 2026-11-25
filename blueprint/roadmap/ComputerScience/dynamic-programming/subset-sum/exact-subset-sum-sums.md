# Attainable sums in exact subset sum

Given a list $x = (x_1, \dots, x_n)$ of natural
numbers and a target $t \in \mathbb{N}$, this timed procedure starts from the list $L_0 = (0)$
and, for $i = 1, \dots, n$ in order, forms $L_i$ from $L_{i-1}$ in four steps: add $x_i$ to
every entry of $L_{i-1}$; merge $L_{i-1}$ with this shifted list (the standard merge of two
lists, comparing entries with $\le$); delete adjacent repeated values; and keep only the values
at most $t$. It returns $L_n$. The counted events are the initial assignment and, in each
phase, one event per addition, one per merge comparison, one per comparison of adjacent
values, one per comparison with $t$, and one for the phase assignment.
