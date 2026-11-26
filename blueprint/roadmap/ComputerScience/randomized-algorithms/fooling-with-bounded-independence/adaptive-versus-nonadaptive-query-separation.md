# Adaptive t-query tests separate a law with almost uniform t-bit marginals

For every integer $t \ge 1$ there is a distribution $Z$ on exactly $2^{t-1}$ bits such that every marginal of $Z$ on $t$ fixed coordinates is within total variation distance $t/2^t$ of uniform, yet some decision tree of depth at most $t$ accepts every sample of $Z$ and accepts a uniform string with probability exactly $1/2$. Thus the factor $2^t$ in the adaptive bound for almost $t$-wise independence cannot be removed.

## Proof sketch

Read the first $t - 1$ queried bits as an address selecting a data bit and accept iff the selected bit has a prescribed value forced in $Z$. Pairing addresses along edges of the cube so that both addresses of a pair share a data bit, with opposite forced values on the two sides, attains length $2^{t-1}$; a fixed projection hiding the edge coordinate sees an exactly uniform comparison, and the remaining addresses add at most $t$ mismatch events of probability $2^{-t}$.

## Depends on

- [Adaptive bit tests of almost t-wise independent distributions](adaptive-tests-of-almost-t-wise-independence.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", public draft of Chapters 7–8, March 2007.
