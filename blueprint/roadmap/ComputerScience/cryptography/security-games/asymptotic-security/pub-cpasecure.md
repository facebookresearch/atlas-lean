# CPA security of public-key encryption families

A family of public-key encryption schemes is CPA secure against a class of admissible adversary
families (Katz and Lindell, Definition 11.2) when every admissible family of eavesdropping
adversaries, with coins in given nonempty sets $R_n$, has negligible advantage in
$\mathrm{PubK}^{\mathrm{eav}}$. These adversaries make no oracle queries, so the class is given
explicitly: a class that bounds only the number of queries admits every family, and then the notion
is security against unbounded adversaries rather than the probabilistic polynomial-time notion. The
message spaces must be nonempty.
