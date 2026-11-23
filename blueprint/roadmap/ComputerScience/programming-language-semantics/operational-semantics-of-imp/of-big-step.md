# Big-step executions terminate in small steps

For every IMP command $c$ and states $s$ and
$s'$, if $c$ evaluates from $s$ to $s'$ in the big-step semantics, then $c$ started in $s$
terminates by small steps in $s'$: finitely many small steps lead from the configuration $(c, s)$
to $(\mathrm{skip}, s')$.
