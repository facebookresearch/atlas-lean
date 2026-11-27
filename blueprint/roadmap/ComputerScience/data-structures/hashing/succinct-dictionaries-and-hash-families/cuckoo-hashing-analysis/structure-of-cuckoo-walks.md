# Structure of cuckoo displacement walks

When a key is inserted into a valid two-table cuckoo placement, the sequence of displaced keys forms a walk in the cuckoo graph starting at the new key's edge. If the insertion does not enter a closed loop (a set of keys whose two-slot choices cover fewer slots than keys, that is, a component of the cuckoo graph with two cycles) and performs $t$ displacements, then this walk contains a sequence of at least $t/3$ consecutive distinct keys forming a simple path in the cuckoo graph that starts at one of the new key's two slots. Hence a long displacement walk exhibits a long simple path or a closed loop, and a walk that never terminates exhibits a component with two cycles.

## Proof sketch

Follow the displacements: until a slot is revisited, the keys are distinct. At the first revisit, of the key $x_i$ that becomes nestless for the second time at step $j > i$, the walk retraces $x_{i-1}, \dots, x_2$ back to their original cells and the new key $x_1$ becomes nestless again at step $i + j - 1$, then continues from its other slot. If the walk has $p < i + j$ steps, its first $j - 1 \ge p/2$ keys are distinct; otherwise one of the runs $x_1, \dots, x_{j-1}$ and $x_{i+j-1}, \dots, x_p$, both starting with the new key, has length at least $p/3$, and without a closed loop the second run consists of distinct keys.

## Depends on

- [Cuckoo graph of a key set](cuckoo-graph.md)

## Sources

- R. Pagh and F. F. Rodler, "Cuckoo Hashing", Journal of Algorithms 51(2), 2004 (Lemma 1).
