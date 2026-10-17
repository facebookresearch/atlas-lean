---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Concurrency.Banker.System.request_safe
---

# Request safe

Granted requests lead to safe states.

## Depends on

- [System](system.md)
- [Safe](safe.md)
- [Request](request.md)

## Proof depends on

- [Grant](grant.md)
- [Need](need.md)
- [The request algorithm grants exactly the safe requests within the claim and the free resources](request-eq-some-iff.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Concurrency.Banker](../../../../../sources/v2/CSLibExt.md)
