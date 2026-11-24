# Motor Incidence

Ground-deleted, head-positive incidence matrix of the series motor loop. Nodes: `0` supply
terminal, `1` internal resistance/inductance junction, `2` inductance/back-EMF junction.
Branches (head, tail): `0` supply source (ground, node `0`), `1` armature resistance (node `0`,
node `1`), `2` armature inductance (node `1`, node `2`), `3` back-EMF source (node `2`,
ground).
