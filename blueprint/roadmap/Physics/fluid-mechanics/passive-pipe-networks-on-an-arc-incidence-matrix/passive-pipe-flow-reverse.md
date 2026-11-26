# Reversing a passive pipe flow

Let a pipe network have finitely many nodes and arcs, arc resistances $r$, signed arc flows $q$, node inflows $d$ and heads $h$, and suppose $(q, h)$ is a passive pipe flow: flow conservation $Bq = d$ for the incidence matrix $B$, the head-loss law $-(B^\top h)_e = r_e q_e |q_e|$, and $r_e \ge 0$. Then reversing every arc and replacing $q$ by $-q$ gives a passive pipe flow with the same $d$ and $h$.
