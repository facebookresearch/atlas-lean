# Polynomial-query CPA security

A family of private-key encryption schemes, one for each security parameter $n$, is
polynomial-query CPA secure when every family of chosen-plaintext adversaries with coins in given
nonempty sets $R_n$ that makes polynomially many queries has negligible CPA advantage (the
experiment of Katz and Lindell, Definition 3.22). The adversaries' own computation is unbounded, so
this is not the probabilistic polynomial-time notion of Definition 3.22. The message spaces must be
nonempty; with empty message spaces or coin sets there would be no adversaries.
