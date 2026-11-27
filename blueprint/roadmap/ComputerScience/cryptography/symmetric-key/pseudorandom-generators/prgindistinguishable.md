# Pseudorandomness relative to a class of distinguishers

A family of generators $G_n : S_n \to Y_n$ is indistinguishable from uniform relative to a class of
admissible distinguisher families, with coins in given nonempty sets $R_n$, when every admissible
family has negligible PRG advantage. This is the pseudorandomness condition of Katz and Lindell,
Definition 3.14, with the admissible class as a parameter. Definition 3.14 also requires the generator
to be computable in deterministic polynomial time and the distinguishers to run in probabilistic
polynomial time; the first is not imposed here, and the second is whatever the class encodes.
