# Structure of cuckoo displacement walks

When a key is inserted into a valid two-table cuckoo placement, the sequence of displaced keys forms a walk in the cuckoo graph starting at the new key's edge. If the insertion performs $t$ displacements, then this walk contains a sequence of at least $t/3$ consecutive distinct keys forming a simple path in the cuckoo graph that starts at one of the new key's two slots. Hence a long displacement walk exhibits a long simple path, and a walk that never terminates exhibits a component with two cycles.

## Proof sketch

Follow the displacements: until a slot is revisited, the keys are distinct. At the first revisit the walk retraces previously moved keys back to the start and then continues from the other slot of the new key; at least one of the three phases (before the revisit, the retracing, after it) contains a third of the displacements and consists of distinct keys along a simple path.

## Depends on

- [Cuckoo graph of a key set](cuckoo-graph.md)

## Sources

- R. Pagh and F. F. Rodler, "Cuckoo Hashing", Journal of Algorithms 51(2), 2004.
