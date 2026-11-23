# CPA experiment for key encapsulation

The experiment $\mathrm{KEM}^{\mathrm{cpa}}$ (Katz and Lindell, Section 11.3) draws a uniform bit
selecting the real or a uniform key, runs the left-or-right KEM experiment with that bit, and outputs
$1$ when the adversary guesses it.
