# Slit Domain nonempty

The negative real point `-1/2` belongs to the slit domain, so it is nonempty for every finite
slit family.

Here `E` is the displayed finite slit family with `0 ≤ inner(i) ≤ outer(i) ≤ 1`; no disjointness or
positive interval length is assumed.

```lean
theorem slitDomain_nonempty : E.slitDomain.Nonempty
```
