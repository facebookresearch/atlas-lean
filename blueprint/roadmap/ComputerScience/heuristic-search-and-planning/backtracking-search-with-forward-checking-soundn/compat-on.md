# Compatibility against a list of arcs

Compatibility of the assignments $x = a$ and $y = b$ checked against a supplied list of arcs: every
listed arc between $x$ and $y$, in either orientation, allows the pair. Forward checking supplies
the arcs between $x$ and $y$ only, so the full arc list is not rescanned for every candidate value.
