# Public-key CCA experiment

The experiment $\mathrm{PubK}^{\mathrm{cca}}$ (Katz and Lindell, Definition 11.8) draws a uniform
challenge bit $b$, runs the left-or-right public-key chosen-ciphertext experiment with $b$, and
outputs $1$ when the adversary's guess equals $b$.
