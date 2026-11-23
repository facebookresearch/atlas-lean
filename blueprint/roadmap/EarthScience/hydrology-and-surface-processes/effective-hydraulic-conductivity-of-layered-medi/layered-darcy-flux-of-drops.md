# Layered Darcy Flux of drops

Flux recovery from interface drop laws (source direction).
Let `head 0, ..., head n` be continuous interface heads in flow
order and let `q` be a supplied common steady Darcy flux satisfying
the per-layer drop law `head i - head (i + 1) = q * (L i / K i)`
for each layer. Then `q` is the total head drop divided by the
summed series resistance. The per-layer Darcy drop relation is an
explicit supplied model assumption, not derived here.
