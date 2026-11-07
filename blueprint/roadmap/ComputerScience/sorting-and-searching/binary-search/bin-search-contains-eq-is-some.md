# Array binary search membership test agrees with binary search

Let $A$ be an array with
entries in a type $\alpha$, let $k \in \alpha$, let $\mathrm{lt}$ be any Boolean-valued comparison
on $\alpha$, and let $\ell$ and $h$ be natural numbers. Lean core's Boolean binary search
membership test for $k$ in $A$, with comparison $\mathrm{lt}$ and bounds $\ell$ and $h$, returns
true exactly when Lean core's array binary search with the same arguments returns some element.
