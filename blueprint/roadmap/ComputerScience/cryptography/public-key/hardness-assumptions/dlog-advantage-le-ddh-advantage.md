# DDH hardness implies discrete-logarithm hardness

If $g$ generates $G$ and $|G| = q$, the discrete-logarithm advantage of a solver $A$ is at most the DDH
advantage of the distinguisher built from the CDH solver built from $A$, plus $1/q$ (Katz and Lindell,
Section 8.3.2).
