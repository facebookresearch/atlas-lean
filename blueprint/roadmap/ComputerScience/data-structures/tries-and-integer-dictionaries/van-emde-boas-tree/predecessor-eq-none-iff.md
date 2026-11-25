# Empty predecessor query in a van Emde Boas tree

Let $t$ be a valid two-level van Emde Boas
tree over the universe $\{0, \dots, m^2 - 1\}$, and let $x$ be in the universe. The predecessor
query for $x$ in $t$ returns no element if and only if $x \le z$ for every $z$ stored in $t$.
