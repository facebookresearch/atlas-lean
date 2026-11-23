# Sortable in k reversals implies at most 2k breakpoints

For natural numbers $k$ and $n$ and a list of integers $\pi$ that [sorts](usortable-in.md) to
$(1, \dots, n)$ in exactly $k$ reversals, the [unsigned breakpoint count](ubreaks.md) satisfies
$b_n(\pi) \le 2k$: a reversal of positions $i \le j$ inside the list removes at most two
breakpoints, and the identity list has none (Shamir and Peer, Lecture 11, Theorem 11.2).
