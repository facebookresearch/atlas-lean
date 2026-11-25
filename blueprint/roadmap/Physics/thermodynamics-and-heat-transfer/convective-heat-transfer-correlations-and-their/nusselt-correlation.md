# Range-guarded empirical Nusselt correlation

An empirical Nusselt correlation consists of:

- a citation (provenance only, not an applicability condition);
- the [flow configuration](flow-configuration.md), hydrodynamic and thermal
  [development](flow-development.md), [property-variation class](property-variation.md),
  [local or averaged tag](averaging-tag.md) and [property temperature](property-temperature.md) it
  was calibrated with;
- a nonempty validity domain of [flow conditions](flow-conditions.md), on which `Re > 0` and
  `Pr > 0`;
- a formula giving a real number for each flow condition in the validity domain, and only there.

The validity domain is calibration evidence supplied with the correlation; nothing asserts that the
formula is physically correct inside or outside it.
