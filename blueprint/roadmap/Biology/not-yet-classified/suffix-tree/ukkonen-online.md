# Ukkonen's on-line construction

**Ukkonen's on-line construction** (Ukkonen 1995, Algorithm 2):
hypotheses are the string `T`, a step count `i` within bounds (`hi`), and a
build procedure `build` giving the state after each prefix with suffix links
(`hbuild`). Conclusion: after `i` symbols the state is the suffix tree of
the length-`i` prefix.

## Sources

- Ukkonen (1995), Algorithm 2.
