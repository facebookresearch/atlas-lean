# Reads of an overwrite-newest register return increasing publications

Consider the overwrite-newest single-slot sampled register with values in a set $V$: its state is either empty, $\bot$, or a pair
$(n, v)$ of a publication number and a value; the $k$-th $\mathsf{Publish}(v)$ sets the state to $(k, v)$, whatever it was, and
an atomic $\mathsf{Read}$ returns the state and empties it. A read is successful when it returns a pair. Then, starting from the empty register $\bot$,
for every finite sequence of $\mathsf{Publish}$ and $\mathsf{Read}$ events:

1. a successful read that returns $(n, v)$ returns exactly the value of the $n$-th publication;
2. the publication numbers returned by successive successful reads are strictly increasing, so no publication is returned twice;
3. every publication that no read returns either is still held in the register at the end of the sequence or was followed by a
   later publication before any read.

After the $n$-th publication the next event that touches the register is either a read, which returns $(n, v)$ and empties the
slot, or the $(n+1)$-th publication, which overwrites it; this gives all three claims by induction on the sequence.

## Sources

- H. Kopetz, *Real-Time Systems: Design Principles for Distributed Embedded Applications*, 2nd edition, Springer, 2011, Chapter 4 (state messages with update-in-place semantics).
- N. A. Lynch, *Distributed Algorithms*, Morgan Kaufmann, 1996, Chapter 8 (automata, traces and simulation relations).
