---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Concurrency.Banker.System.request
---

# Request

The resource-request algorithm: process `p` asks for `req` more resources
out of `available`. The request is granted, returning the new free vector and
system, when `p` is pending (in a duplicate-free list), the request is within
`p`'s remaining need and the free resources, and the resulting state is safe.
`none` covers the error case of the textbook algorithm (a request beyond the
remaining claim), the cases where the process must wait, and malformed input (a
requester that is not pending, or a pending list with repetitions).

## Depends on

- [System](system.md)

## Proof depends on

- [Grant](grant.md)
- [Need](need.md)
- [Safety Check](safety-check.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Concurrency.Banker](../../../../../sources/v2/CSLibExt.md)
