# The de Bruijn round trip

If `names` has no repetition and `t` is scoped at the length of
`names`, then `ofLocallyNameless names (toLocallyNameless names t) = t`.
