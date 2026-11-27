# Input shares agree with the input polynomials

Let `F` be a field and `Party` a finite type of parties with Shamir parameters
`params`. For every input `k` and party `j`, `inputShares params x tapeIn k j`
equals the evaluation of the input polynomial `inputPolys params x tapeIn k`
at `params.point j`.
