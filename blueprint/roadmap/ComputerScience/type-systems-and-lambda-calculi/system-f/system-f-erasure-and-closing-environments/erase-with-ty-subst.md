# Untyped erasure is invariant under type substitution

For every type substitution $\tau$, environment $\eta$ of untyped terms and System F term $t$, the [erasure](erase-with.md) of the [type substitution](../scoped-pure-system-f/ty-subst.md) $t[\tau]$ under $\eta$ equals the erasure of $t$ under $\eta$: type substitution changes no part of the erased term.
