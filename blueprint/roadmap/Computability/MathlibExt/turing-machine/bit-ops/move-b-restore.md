---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.TM2Program.moveB_restore
---

# Restoring after `cmpB`

**Restoring after `cmpB`.** If the scratch stack `t` holds the moved prefix `c` (pushed by
`et`) above old contents `R` that end a block, `moveB t a dt ga` puts the original symbols back on
`a` in `c.length + 1` steps, leaving `R` on `t`. Needs `dt` to read back what `et` pushed and `ga`
to give back the symbols of `a`'s block (`hga`).

## Depends on

- [Ends Bit Block](ends-bit-block.md)
- [Flag](../program/part-01/flag.md)
- [Is Bit Block](is-bit-block.md)
- [Run](../program/part-01/run.md)
- [Move B](move-b.md)

## Proof depends on

- [Take eq map](take-eq-map.md)
- [Move B run](move-b-run.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.BitOps](../../../../../sources/v2/MathlibExt.md)
