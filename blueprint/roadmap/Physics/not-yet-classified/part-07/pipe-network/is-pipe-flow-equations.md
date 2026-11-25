# Pipe-flow equations on a network

Let a finite set of pipes (arcs, parallel pipes allowed) join a finite set of nodes, each pipe $e$ running from a tail node to a head node, with signed incidence matrix $B_{ve} = [\mathrm{head}(e) = v] - [\mathrm{tail}(e) = v]$. Given resistances $r_e$, pipe flows $q_e$, nodal net inflows $d_v$ and nodal heads $h_v$, the pipe-flow equations hold when
- $Bq = d$ (flow balance at every node), and
- for every pipe $e$, the head drop $-(B^\top h)_e = h_{\mathrm{tail}(e)} - h_{\mathrm{head}(e)}$ equals $r_e\,q_e|q_e|$.

No sign condition is placed on the resistances.
