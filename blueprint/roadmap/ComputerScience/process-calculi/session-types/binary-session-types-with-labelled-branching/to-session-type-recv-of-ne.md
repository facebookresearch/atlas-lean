# Receives at another sort have no session type

For a sort type with decidable equality, if the payload sort of a receive differs from the passive sort, the partial map to payload-free session types at that passive sort sends `recv payload next` to `none`.
