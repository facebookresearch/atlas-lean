# Count Run?

Transcription of CPython's `count_run`.

`base` is the signed pointer-like index corresponding to `slo->keys`, and
`nremaining` is the asserted-positive, signed-`Py_ssize_t`-representable
remaining length. `none` represents an invalid assertion input or a failed
modeled access; `fuelExhausted` is kept distinct so the later safety theorem
can prove that the chosen bounds suffice.
