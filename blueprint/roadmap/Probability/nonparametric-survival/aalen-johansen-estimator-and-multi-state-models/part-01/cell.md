# Cell index set of a grouped competing-risks record

For natural numbers $k$ and $r$ (grid indices $\{0, \dots, k-1\}$, causes $\{0, \dots, r-1\}$), the cell index set is the disjoint union

$$\mathrm{Cell}_{k,r} = \big(\{0, \dots, k-1\} \times \{0, \dots, r-1\}\big) \sqcup \{0, \dots, k-1\}.$$

An element $(j, c)$ of the first summand is the event cell "observed failure from cause $c$ at grid index $j$"; an element $j$ of the second summand is the at-risk cell "at risk at grid index $j$".
