# OR-rule value is true exactly when some processor writes true

For every $w : \mathrm{Fin}\,n \to \mathrm{Bool}$, the OR-rule cell value $\bigvee_{i} w_i$ equals $\mathrm{true}$ if and only if there is a processor $i \in \mathrm{Fin}\,n$ with $w_i = \mathrm{true}$.
