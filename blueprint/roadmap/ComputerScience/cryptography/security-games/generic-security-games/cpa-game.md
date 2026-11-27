# CPA indistinguishability experiment

The experiment $\mathrm{PrivK}^{\mathrm{cpa}}$ (Katz and Lindell, Definition 3.22) draws a uniform
challenge bit $b$, runs the left-or-right chosen-plaintext experiment with $b$, and outputs $1$ when
the adversary's guess equals $b$. The eavesdropping experiment $\mathrm{PrivK}^{\mathrm{eav}}$
(Definition 3.8) is the case of adversaries that make no queries.
