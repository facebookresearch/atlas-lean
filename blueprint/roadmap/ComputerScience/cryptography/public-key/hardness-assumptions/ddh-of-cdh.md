# DDH distinguisher from a CDH solver

From a CDH solver $A$, the DDH distinguisher on input $(X, Y, Z)$ outputs $1$ exactly when
$A(X, Y) = Z$, with the same coins (Katz and Lindell, Section 8.3.2: if CDH is easy, then so is DDH).
