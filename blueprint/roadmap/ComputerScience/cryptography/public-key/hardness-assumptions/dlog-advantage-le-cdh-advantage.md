# CDH hardness implies discrete-logarithm hardness

If $g^q = 1$, the CDH solver built from a discrete-logarithm solver $A$ succeeds whenever $A$ does, so
the discrete-logarithm advantage of $A$ is at most the CDH advantage of the solver built from it
(Katz and Lindell, Section 8.3.2).
