# Bisimulation-invariant formulas

A first-order formula $\alpha$ over the modal language,
with one variable $x$ and no other free variables, is bisimulation-invariant if for all Kripke
models $M$ and $N$ over the same atoms, every bisimulation $Z$ between $M$ and $N$ and all
worlds $w$ of $M$ and $v$ of $N$ with $Z(w, v)$, the formula $\alpha$ holds in $M$ (viewed as
a structure for the modal language) at $x = w$ if and only if it holds in $N$ at $x = v$.
