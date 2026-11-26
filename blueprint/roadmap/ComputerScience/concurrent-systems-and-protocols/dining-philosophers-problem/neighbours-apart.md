# Neighbours-apart formula

For a philosopher $i \in \{0, 1, 2\}$, the CTL formula
$\neg(p_i \wedge p_{i+1})$ over the atoms $p_0, p_1, p_2$ (one per philosopher), with indices
modulo $3$. Under the valuation in which $p_j$ holds when philosopher $j$ eats, it says that the
neighbouring philosophers $i$ and $i + 1$ do not eat at the same time.
