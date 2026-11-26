# Execution witnesses of the axiomatic x86-TSO model

An execution witness for events of
type $E$ consists of a memory order $\mathrm{mo}$ and a reads-from map $\mathrm{rf}$, relations on
the events, where $(w, r) \in \mathrm{rf}$ means that the read $r$ reads from the write $w$, and an
initial state, a partial map from locations to values (Owens, Sarkar and Sewell, *TPHOLs 2009*,
Section 3.2).
