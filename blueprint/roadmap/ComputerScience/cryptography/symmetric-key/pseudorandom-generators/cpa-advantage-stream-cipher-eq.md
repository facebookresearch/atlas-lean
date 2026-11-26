# The stream cipher is eavesdropping-secure if the PRG is pseudorandom

For every eavesdropper $A$, a chosen-plaintext adversary that makes no queries, the CPA advantage of
$A$ against the stream cipher, $|p - \tfrac{1}{2}|$ where $p$ is the probability that $A$ guesses a
uniform challenge bit in the CPA indistinguishability experiment, equals the PRG advantage of the
distinguisher built from $A$ (Katz and Lindell, Theorem 3.18, as an equality).
