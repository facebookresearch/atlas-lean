# Contextual approximation

Given a context algebra and an observation (program judgments, an operational semantics at each of them and an outcome relation), a term $t$ contextually approximates a term $u$ of the same judgment when, for every program judgment $k$, every context $C$ from their judgment to $k$ and every outcome $o$, if $C[t]$ yields $o$ then $C[u]$ yields $o$. A program yields $o$ when it reaches, in finitely many steps, a final configuration with outcome $o$. The terms need not be programs themselves; only their pluggings are run.
