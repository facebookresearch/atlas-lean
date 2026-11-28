# Alloc

The heap that binds the `i`-th name of `ps` to the `i`-th right-hand side of `bs`, in which
the `j`-th name bound by `bs` is replaced by the `j`-th name of `ps`.

Both pairings use `List.zip`, which stops at the end of the shorter list. When `ps` has fewer
names than `bs` has bindings, only the first `ps.length` bindings are allocated, and a bound name
that is not among the first `ps.length` bound names is left in place; when `ps` has more names,
the extra names are ignored. A name that `bs` binds more than once is replaced by the name paired
with its first occurrence. The `let` rule of `Eval` allocates only with exactly one name per
binding, the names distinct and fresh and the bound names distinct, so none of this arises
there.
