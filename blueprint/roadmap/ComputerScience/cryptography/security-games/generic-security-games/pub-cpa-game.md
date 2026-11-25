# Public-key eavesdropping experiment

The experiment $\mathrm{PubK}^{\mathrm{eav}}$ (Katz and Lindell, Definition 11.2) draws a uniform
challenge bit $b$, runs the left-or-right public-key eavesdropping experiment with $b$, and outputs
$1$ when the adversary's guess equals $b$. For public-key schemes, security in this experiment is
equivalent to CPA security by Proposition 11.3 (stated here without proof).
