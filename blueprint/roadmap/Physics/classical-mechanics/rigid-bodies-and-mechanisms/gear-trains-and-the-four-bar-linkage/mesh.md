# Gear mesh between two consecutive shafts

A mesh consists of positive integers `z` and `z'`, the numbers of teeth of its gear on the upstream
shaft and of its gear on the downstream shaft, and a [mesh kind](mesh-kind.md), with `z < z'` when
the mesh is internal: the downstream gear is then the ring and has strictly more teeth than the
upstream pinion. The words upstream and downstream (driver and driven) record positions in the
train, not the direction of power flow.
