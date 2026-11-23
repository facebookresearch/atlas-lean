# Public-key CPA experiment

The experiment $\mathrm{PubK}^{\mathrm{cpa}}$ (Katz and Lindell, Section 11.2.2) draws a uniform
challenge bit $b$, runs the left-or-right public-key chosen-plaintext experiment with $b$, and
outputs $1$ when the adversary's guess equals $b$.
