# `Sig-forge`

**`Sig-forge`** (Katz and Lindell, Definition 12.2): `(pk, sk) ← Gen`, the forger gets `pk`
and the oracle `Sign_sk` and outputs `(m, σ)`; the experiment outputs `1` when
`Vrfy_pk(m, σ) = 1` and `m` was never queried.
