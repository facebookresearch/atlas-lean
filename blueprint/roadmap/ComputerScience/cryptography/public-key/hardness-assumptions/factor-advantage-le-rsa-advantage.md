# RSA hardness implies factoring hardness

For every key-generation distribution, the RSA inverter built from a factoring algorithm $F$ succeeds
whenever $F$ does, whatever the challenge, so the factoring advantage of $F$ is at most the
RSA-inversion advantage of the inverter (Katz and Lindell, Section 8.2.4). The converse, that an RSA
inverter yields a factoring algorithm, is an open problem.
