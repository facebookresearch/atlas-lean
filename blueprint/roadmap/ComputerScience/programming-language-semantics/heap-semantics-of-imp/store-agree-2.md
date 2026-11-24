# Heap executions only change assignable variables

If a heap configuration $(c, s, h)$
reaches a heap configuration $(c', s', h')$ in zero or more heap steps, then $s'(x) = s(x)$ for
every variable $x$ outside the set of variables that $c$ may assign to.
