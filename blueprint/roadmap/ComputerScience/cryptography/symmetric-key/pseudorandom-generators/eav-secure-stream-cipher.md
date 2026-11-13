# Asymptotic eavesdropping security of the stream cipher

**Asymptotic eavesdropping security of the stream cipher** (Katz and Lindell,
Theorem 3.18): if the generator family is indistinguishable from uniform against a class `AdmD`
of distinguisher families containing the reductions of all admissible eavesdroppers, the stream
cipher family is secure against the admissible eavesdroppers. Expansion is not needed for
security, so it is not a hypothesis; `eavSecure_streamCipher_of_prgSecure` is the corollary from
`PRGSecure`.
