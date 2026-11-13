# Sigma

The **Schnorr identification protocol** as a Sigma protocol (Katz and Lindell, Section 12.5,
Figure 12.2): statements are group elements `y` with `y ^ q = 1`, witnesses are discrete
logarithms `x` with `g ^ x = y`, the prover's coins and the challenge are in `ZMod q`, the
commitment is `g ^ k`, the answer is `r x + k`, and the verifier checks `Schnorr.Accepts`
(`sigma_verify_eq_true_iff`).
