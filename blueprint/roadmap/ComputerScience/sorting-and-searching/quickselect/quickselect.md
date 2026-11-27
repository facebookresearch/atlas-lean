# Quickselect

Deterministic quickselect takes a list $L$ over a linear order and a
zero-based rank $k$ and returns an element or no element, together with its cost, the number
of element comparisons it makes. If $k \ge |L|$, it returns no element at no cost. Otherwise
it runs the following recursion, starting from the list $L$ and the rank $k$. On an empty list
it returns no element. On a list with first entry $p$ and remaining entries $T$, and a rank
$r$, it forms the three-way partition of $T$ around $p$, with blocks $B$, $E$, $A$ of entries
below, equal to and above $p$, at a cost of $|T|$ comparisons. If $r < |B|$, it recurses on
$B$ with rank $r$; if $|B| \le r < |B| + |E| + 1$, it returns $p$; otherwise it recurses on
$A$ with rank $r - (|B| + |E| + 1)$.

The recursion carries a fuel counter that starts at $|L|$ and drops by one per call, and it
returns no element when the fuel is exhausted; since every recursive call is on a strictly
shorter list, the fuel never runs out on a nonempty list.
