# Sim Tape

Like `runTape`, but the encryption of `m` with randomness `r` is itself an oracle algorithm
`encQ m r` querying a keyed function (a PRF or a block cipher); the result is one oracle algorithm
for that keyed function.
