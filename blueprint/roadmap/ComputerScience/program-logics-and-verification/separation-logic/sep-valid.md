# Separation-logic triple validity

For heap assertions $P$, $Q$ and a heap command $c$,
the triple $\lbrace P \rbrace\ c\ \lbrace Q \rbrace$ is valid (in the fault-avoiding sense)
when, for every store $s$ and heap $h$ with $P(s, h)$, the configuration $(c, s, h)$ is safe
(no configuration reachable from it is stuck at a command other than $\mathtt{skip}$), and
whenever $(c, s, h)$ reaches $(\mathtt{skip}, s', h')$ in finitely many heap steps,
$Q(s', h')$ holds.
