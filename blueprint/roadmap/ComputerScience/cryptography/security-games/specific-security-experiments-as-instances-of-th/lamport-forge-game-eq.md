# Lamport forgery experiment as a signature-forgery experiment

For every one-query Lamport forger `A` with uniform coins, the Lamport
one-time forgery experiment for `f` equals the signature-forgery experiment
`Sig-forge` of `lamport f` against the embedded forger `A.toSigForger` (Katz
and Lindell, Definition 12.2 and Section 12.6.1).
