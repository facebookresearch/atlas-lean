# Typed context algebra

A typed context algebra over a type $J$ of judgments consists of a family of terms at each judgment, a family of contexts from a judgment $j$ to a judgment $k$, and plugging, which puts a term at $j$ into a context from $j$ to $k$ to give a term at $k$. It also has a hole context at every judgment and composition of contexts, with the two plugging laws: plugging into the hole returns the term, and plugging into a composite $D \circ C$ is plugging into $C$ and then into $D$.
