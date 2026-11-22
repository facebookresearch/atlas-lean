# Walking up two paths in lockstep

The lockstep walk recomputes from two nodes $x$ and $y$ at the same position, with paths $p$ and $q$,
level by level as in recomputing a root. At each level where both use a path entry it compares the
two pairs of hash inputs: if they differ and hash to the same value, it returns them as a collision
pair, and otherwise it continues one level up. A promoted level uses no entries, and the walk returns
nothing if a path runs out or the levels are used up.
