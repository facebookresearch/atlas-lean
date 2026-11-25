# Grounded DC load-flow solve and flow transfer

Consider a network with branch susceptances $b_e > 0$ whose branches connect all nodes, incidence matrix $B$, weighted Laplacian $L_b = B\,\mathrm{diag}(b)\,B^\top$, a reference node $r$, and injections $p$ with $\sum_v p_v = 0$. Then:

1. there is a unique $\theta$ with $\theta_r = 0$ and $L_b \theta = p$;
2. the grounded angles (solve of the reduced system with the reference row and column removed, $\theta_r = 0$) vanish at $r$ and satisfy $L_b \theta = p$;
3. their DC injection $B f$, with $f = \mathrm{diag}(b) B^\top \theta$, equals $p$;
4. their branch flows are $f_e = b_e(\theta_{\text{tail}(e)} - \theta_{\text{head}(e)})$, and every solution of $L_b \theta = p$ gives the same flows;
5. on every branch, the lossless unit-voltage AC sending-end real power $P_e$ at the grounded angles satisfies $|P_e - f_e| \le b_e |\theta_{\text{tail}(e)} - \theta_{\text{head}(e)}|^3/6$.
