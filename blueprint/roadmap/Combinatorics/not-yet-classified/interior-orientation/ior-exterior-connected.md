# Ior Exterior Connected

Every site outside `K` is joined, by a lattice path avoiding the face loop of the orbit of `a`,
to a site weakly left of the whole loop.

This asks it also for sites outside `K` that lie on the loop, so it fails whenever the loop passes
through a site outside `K`: for the unit cell (`StatMech.Lattice.exc_oldExteriorConnected_false`)
and for the domino. `StatMech.Lattice.exc_OffSupportReachesExterior` is the corrected form.
