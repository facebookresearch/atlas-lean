# Exit Dart same Orbit iff head Same Component

For an interface-connected finite origin cluster, the left exit dart lies on the boundary orbit
of the right exit dart if and only if the heads of the two darts lie in one connected component of
the complement of the cluster. The forward direction holds without interface connectedness
(`StatMech.Lattice.head_compl_of_exitDartsSameOrbit`). Interface connectedness is a hypothesis; the
library proves it only for one-site sets (`StatMech.Lattice.ifc_interfaceConnected`).
