# The CPA reduction

**The CPA reduction** (Katz and Lindell's adversary `A_Enc`, Section 4.5): sample a MAC key
`k₂`, run the CCA adversary with encryption queries forwarded to the CPA oracle and tagged with
`k₂`, and decryption queries answered from the table of answers; the challenge ciphertext `c`
is completed to `(c, Mac_{k₂}(c))`.
