# Soundness invariant of CDCL

For a CNF formula $F$, a CDCL [state](state.md) satisfies the invariant when every learned clause is resolution-derivable from $F$; if the state is in conflict, the conflict clause is resolution-derivable from $F$ and every literal of it is false on the trail; and [every propagation on the trail is justified](reasons-valid.md): its reason clause is derivable from $F$, contains the propagated literal, and has every other literal false on the older part of the trail.
