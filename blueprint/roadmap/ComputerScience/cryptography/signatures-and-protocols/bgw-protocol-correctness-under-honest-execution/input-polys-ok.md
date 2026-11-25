# Input polynomials share their inputs

Let `F` be a field and `Party` a finite type of parties with Shamir parameters
`params`. For every input `k`, the input polynomial `inputPolys params x
tapeIn k` evaluates to `x k` at `0` and has natural degree at most
`params.threshold`.
