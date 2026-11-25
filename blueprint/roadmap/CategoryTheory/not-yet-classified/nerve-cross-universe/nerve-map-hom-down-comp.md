# Nerve Map Hom Down comp

`nerveMapHomDown` sends a composite of arbitrary-hom-universe functors
to the composite of their nerve maps.

The `nolint` is a documented false positive: the left-hand side pins
cross-universe `max`-levels, so simpNF's self-application check cannot match
it, but the lemma does fire at concrete universe levels (pinned by the
`LegacyCompatibility` test closing by `simp` alone).
