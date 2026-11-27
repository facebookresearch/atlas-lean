# Capture-avoiding filling of a process context

The capture-avoiding filling of a [context](context.md) $C$ with a process $P$ replaces the hole by $P$ [lifted](../the-calculus-syntax-substitution-structural-cong/lift-proc.md) once above $0$ for each binder of $C$ (input or restriction) above the hole: $[\,]\{P\} = P$, $(a(\cdot).C)\{P\} = a(\cdot).C\{\uparrow_0 P\}$, $(\nu C)\{P\} = \nu\,C\{\uparrow_0 P\}$, and the filling commutes with the other constructors. Each binder of the context shifts the dangling names of the hole, while the binders internal to $P$ are untouched.
