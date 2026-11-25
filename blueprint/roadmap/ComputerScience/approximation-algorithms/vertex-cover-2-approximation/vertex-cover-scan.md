# Vertex cover scan

Given a finite set $C$ of vertices and a list of pairs of vertices,
the scan processes the pairs in order, starting from the cover $C$ and charging one time unit
per pair. A pair $(u, v)$ is covered when $u$ or $v$ is already in the current cover; a covered
pair is skipped, and an uncovered pair adds both $u$ and $v$ to the cover. The scan returns the
cover reached after the last pair.
