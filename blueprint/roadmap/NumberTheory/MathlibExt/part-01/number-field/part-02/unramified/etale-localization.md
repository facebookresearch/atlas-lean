---
article_id: af_e6febc04f71a20b41ce0a3cb
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: NumberField.IsUnramifiedIn.etale_localization
---

# Etale localization

Semilocal étaleness above an unramified prime: localizing the whole finite
algebra `𝓞 K` at the prime-complement of `p` (inverting everything outside `p`,
keeping all local factors above `p` simultaneously) is étale over the local
base `Localization.AtPrime p`.

This packages the primewise unramified hypothesis used by
`isUnramifiedAtPrime_sup` in the primary Lean source for ATLAS `NumberTheoryI`
target N390, Proposition 19.14. It is the semilocal algebra, not a single local
factor `Localization.AtPrime Q`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.NumberField.Unramified](../../../../../../../sources/v2/MathlibExt.md)
