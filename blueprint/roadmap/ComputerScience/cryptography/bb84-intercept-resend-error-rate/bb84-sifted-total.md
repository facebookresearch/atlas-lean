# Number of sifted rounds in BB84 intercept-resend

Exactly 16 of the 32 values of `(a, cb, ba, be, bb) ∈ Bool⁵` are sifted
rounds, that is, satisfy `bb = ba`. Since exactly 4 of these sifted values
carry an error, the intercept-resend attack causes errors in `4 / 16 = 1 /
4` of the sifted rounds.
