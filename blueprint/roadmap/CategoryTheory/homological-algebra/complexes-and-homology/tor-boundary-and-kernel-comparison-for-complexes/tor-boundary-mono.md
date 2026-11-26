# Exact tensor functors on the term and outgoing image make the Tor boundary monic

Let R be a ring in u, c a complex shape on I in κ, P a complex of right R-modules in v, and N a
left R-module in v. Assume both module categories in v have projective resolutions. Let
i=c.prev(j), B_j=image(d_P(i,j)), Z_j=Z_j(P), and H_j=H_j(P). The boundary/cycle/homology row
0→B_j --β→ Z_j→H_j→0 is short exact. Put β_N=β⊗_R id_N:B_j⊗_R N→Z_j⊗_R N. Assume the functors
P_j⊗_R(-) and image(d_P(j,c.next(j)))⊗_R(-), from left R-modules in v to abelian groups in v,
preserve homology. The cycle row 0→Z_j→P_j→image(d_P(j,c.next(j)))→0 gives Tor₁^R(Z_j,N)=0. The
long exact sequence then makes δ:Tor₁^R(H_j,N)→B_j⊗_R N mono.
