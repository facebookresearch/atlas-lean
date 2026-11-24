# Nerve Map Common Value comp

`nerveMapCommonValue` sends a composite of arbitrary-hom-universe functors
to the composite of their nerve maps. Its universe levels are explicit, so
callers use this law directly rather than relying on universe inference by `simp`.
