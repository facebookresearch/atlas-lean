# Semantic completeness of the while-loop invariant rule

Let $g$ be a formula and $G$ the set of worlds where it holds. The Hoare triple
$\{P\}\, \mathbf{while}\ g\ \mathbf{do}\ a\, \{Q\}$ holds if and only if there is a set $I$ of worlds
with $P \subseteq I$, $\{I \cap G\}\, a\, \{I\}$ and $I \setminus G \subseteq Q$. One can take for
$I$ the set of worlds reachable from $P$ by iterating the guarded body; it does not depend on $Q$.
The assertions are arbitrary sets of worlds, so this is not a completeness theorem for a language
of assertion formulas.
