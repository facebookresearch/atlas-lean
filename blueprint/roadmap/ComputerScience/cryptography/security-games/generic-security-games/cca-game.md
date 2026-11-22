# CCA indistinguishability experiment

The experiment $\mathrm{PrivK}^{\mathrm{cca}}$ (Katz and Lindell, Definition 3.33) draws a uniform
challenge bit $b$, runs the left-or-right chosen-ciphertext experiment with $b$, and outputs $1$ when
the adversary's guess equals $b$. That experiment answers $\bot$ to a decryption query for the
challenge ciphertext; this is equivalent to forbidding that query (stated here without proof).
