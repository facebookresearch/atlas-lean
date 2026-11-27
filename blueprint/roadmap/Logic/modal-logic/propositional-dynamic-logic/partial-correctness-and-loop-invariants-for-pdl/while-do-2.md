# Hoare invariant rule for guarded while loops

Let $g$ be a formula and $G$ the set of worlds where it holds. If
$\{I \cap G\}\, a\, \{I\}$, then $\{I\}\, \mathbf{while}\ g\ \mathbf{do}\ a\, \{I \setminus G\}$. This is
partial correctness: it includes exits after zero iterations and does not guarantee termination.
