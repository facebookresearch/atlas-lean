# Polynomial-query CPA security

**Polynomial-query CPA security** of a family of private-key schemes: the experiment of
Katz and Lindell, Definition 3.22, against adversary families making polynomially many oracle
queries with unbounded local computation. This is not the PPT notion of Definition 3.22 (see the
module docstring); the name `CPASecure` is reserved for that. The message and coin types must be
nonempty, or there would be no adversaries (`exists_polyQueryBounded_cpa`).
