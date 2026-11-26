# Asymptotic PRF security relative to a class of distinguishers

A family of keyed functions $F_n : K_n \times X_n \to Y_n$ is PRF-secure relative to a class of
admissible distinguisher families, with uniform coins in finite nonempty sets $S_n$, when every
admissible family has negligible PRF advantage. This is the indistinguishability condition of Katz
and Lindell, Definition 3.25, with the admissible class as a parameter. Katz and Lindell also require
$F_k(x)$ to be computable in deterministic polynomial time and quantify over probabilistic
polynomial-time distinguishers; the first is not imposed here, and the second must be supplied
through the class.
