# Deterministic MAC with canonical verification

Given a key distribution and a deterministic function $F(k, m)$, the deterministic MAC tags $m$
under $k$ as $\mathrm{Mac}_k(m) = F(k, m)$ and accepts $(m, t)$ exactly when $t = F(k, m)$ (Katz and
Lindell, Section 4.2 and Construction 4.5). For such MACs existential unforgeability is already
strong unforgeability (stated here without proof).
