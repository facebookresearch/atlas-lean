---
article_id: af_7a3992be53c3b24d1dac6c06
declaration: structure
origin: cited
statement: formalized
lean: Rat.Place.CompletedFieldBundle
---

# Completed Field Bundle

Bundled carrier together with the `NormedField` / `CompleteSpace`
instances needed for the completed field `ℚ_v`.

Using a bundle avoids a direct dependent family `Place → Type` returning
`Padic p`, which loses the local `Fact` dictionary and causes kernel
declaration mismatches in projected instances. Instance-valued fields use
bracket syntax so the bundle itself carries the instances.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Rat.Place](../../../../../../sources/v2/MathlibExt.md)
