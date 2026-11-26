# The bijection

Suppose every finite set of names misses some name (`[HasFresh Var]`) and
`names` has no repetition. Then `toLocallyNameless names` and `ofLocallyNameless names` are
inverse bijections between the de Bruijn terms scoped at the length of `names` and the locally
closed terms whose free names lie in `names`.
