# Rotation mem weak Core diff strict Core

With original houses `0,1,2` and best-first rankings `1,0,2`, `0,2,1`, `0,1,2`, allocation
`(1,2,0)` is in the weak core but not the strict core. Agents `0` and `2` already have their
first choices; agent `1` alone owns only `1`, worse than its assigned `2`. Yet `{0,1}` can exchange
original houses to improve agent `1` while leaving agent `0` equally well off.
