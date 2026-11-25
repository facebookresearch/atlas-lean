# Array binary search membership test agrees with binary search

Let $A = (a_0, \dots, a_{n-1})$ be an array with entries in a type $\alpha$, let $k \in \alpha$,
let $\mathrm{lt}$ be any Boolean-valued comparison on $\alpha$, and let $\ell$ and $h$ be natural
numbers. Bounded binary search for $k$ in $A$ with comparison $\mathrm{lt}$ and inclusive bounds
$\ell$ and $h$ returns nothing if $\ell \ge n$ or $\ell > h'$, where $h' = \min(h, n - 1)$;
otherwise it searches the index range $[\ell, h']$: at the midpoint $m = \lfloor (lo + hi)/2 \rfloor$
of the current range $[lo, hi]$ it continues with $[m + 1, hi]$ if $\mathrm{lt}(a_m, k)$ (returning
nothing if $m + 1 > hi$), else with $[lo, m - 1]$ if $\mathrm{lt}(k, a_m)$ (returning nothing if
$m = 0$ or $m - 1 < lo$), and otherwise returns the entry $a_m$. The Boolean membership test
performs the same search and returns true when an entry is returned and false otherwise.

For all $A$, $k$, $\mathrm{lt}$, $\ell$ and $h$, the membership test returns true exactly when the
bounded binary search with the same arguments returns some entry.
