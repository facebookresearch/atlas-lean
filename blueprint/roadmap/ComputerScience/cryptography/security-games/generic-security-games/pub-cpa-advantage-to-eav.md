# Eavesdropping security implies CPA security for public-key encryption

**Eavesdropping security implies CPA security for public-key encryption** (Katz and Lindell,
Proposition 11.3), as an exact equality: for a scheme with encryption `Enc_pk(m) = encR pk m ρ`
for uniform `ρ`, a CPA adversary making at most `n` encryption queries has exactly the advantage of
the eavesdropper `A.toEav encR n` that simulates its oracle.
