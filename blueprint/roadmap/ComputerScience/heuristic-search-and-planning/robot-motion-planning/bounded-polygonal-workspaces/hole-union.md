# Union of hole regions

For a finite list of simple polygons in the plane, the hole union is the union of their regions, defined recursively: the empty list gives $\emptyset$, and a list with head $h$ and tail $t$ gives $R_h \cup \mathrm{holes}(t)$, where $R_h$ is the region of $h$.
