# Sends at another sort have no session type

For a sort type with decidable equality, if the payload sort of a send differs from the passive sort, the partial map to payload-free session types at that passive sort sends `send payload next` to `none`.
