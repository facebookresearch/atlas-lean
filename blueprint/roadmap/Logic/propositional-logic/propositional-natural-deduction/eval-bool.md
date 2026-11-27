# Truth-table evaluation

Given a Boolean valuation $v$ of the atoms, the truth value of a
proposition is computed recursively: an atom $x$ has value $v(x)$, $A \wedge B$ is true iff both
$A$ and $B$ are, $A \vee B$ is true iff at least one of them is, and $A \to B$ is true iff $A$ is
false or $B$ is true. Falsum $\bot$, when present, is itself an atom, so its value $v(\bot)$ is
part of the valuation and need not be false.
