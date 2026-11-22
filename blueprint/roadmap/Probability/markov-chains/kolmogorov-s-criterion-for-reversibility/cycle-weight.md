# Cycle weight

Let $P$ be an irreducible stochastic matrix on the states
$\{0, \dots, M\}$ and fix a reference state $i_0$. The cycle weight of a state $j$ relative to
$i_0$ is the product of the ratios $P(x, y) / P(y, x)$ over consecutive states $x, y$ along a
path (a finite list of states) from $i_0$ to $j$ whose product of transition probabilities
$P(x, y)$ over consecutive states is positive, where a ratio with $P(y, x) = 0$ counts as $0$;
such a path exists by irreducibility, and one is fixed by choice.

For chains satisfying Kolmogorov's cycle condition this value does not depend on the chosen path,
and the weights give a reversible measure.
