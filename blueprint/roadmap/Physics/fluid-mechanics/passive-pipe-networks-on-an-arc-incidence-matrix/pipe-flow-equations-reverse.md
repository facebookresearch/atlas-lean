# Reversing a pipe network

Let a network have finite node and arc sets, arc tails and heads, resistance coefficients $r_e$, signed arc flows $q_e$, net node inflows $d_v$ and node heads $h_v$, satisfying the pipe-flow equations: $B q = d$ for the node–arc incidence matrix $B$, and $-B^{\mathsf T} h = (r_e\,q_e\,|q_e|)_e$. Then reversing every arc orientation and replacing $q$ by $-q$ gives a solution of the pipe-flow equations with the same node inflows and heads.
