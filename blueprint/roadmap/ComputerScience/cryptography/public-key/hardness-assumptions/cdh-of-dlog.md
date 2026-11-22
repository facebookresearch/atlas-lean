# CDH solver from a discrete-logarithm solver

From a discrete-logarithm solver $A$, the CDH solver on input $(X, Y)$ computes $x' = A(X)$, with the
same coins, and outputs $Y^{x'}$ (Katz and Lindell, Section 8.3.2: if the discrete-logarithm problem
is easy, then so is CDH).
