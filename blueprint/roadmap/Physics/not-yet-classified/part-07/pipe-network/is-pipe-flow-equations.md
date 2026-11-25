# Pipe-flow equations on a network

Let a finite set of pipes (arcs, parallel pipes allowed) join a finite set of nodes, each pipe $e$ running from a tail node to a head node, with incidence matrix $B$. Given resistances $r_e$, pipe flows $q_e$, nodal net inflows $d_v$ and nodal heads $h_v$, the pipe-flow equations hold when
- $Bq = d$ (flow balance at every node), and
- for every pipe $e$, the head drop $-(B^\top h)_e$ from tail to head equals $r_e\,q_e|q_e|$.

The resistances are unconstrained, so a negative resistance (an active element) can satisfy the equations.
