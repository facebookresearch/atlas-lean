# Signer Of

The stateful signer for the Lamport public keys `pks`, with `sg i m` the Lamport signature
on `m` under key `i`: at counter `i < N` it returns `(i, pks i, sg i m, authPath i)`; once the
keys are used up it returns `none`.
