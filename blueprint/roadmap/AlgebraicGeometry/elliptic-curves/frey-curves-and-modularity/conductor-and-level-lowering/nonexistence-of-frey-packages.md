# No normalized Frey package exists

There is no tuple of nonzero integers $a,b,c$ and prime $p\ge5$ with $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a\equiv3\pmod4$ and $2\mid b$.

## Proof depends on

- [Frey irreducibility](../torsion-and-irreducibility/irreducibility-of-frey-torsion.md)
- [Frey modularity](../trace-modularity-and-lifting/trace-matching-modularity-of-frey-curves.md)
- [Level lowering to a nonzero form](nonzero-level-two-cusp-form-from-frey-representation.md)
- [Vanishing at level two](../../../../NumberTheory/modular-forms-q-series/modular-forms/weight-two-cusp-forms-on-2/s2-gamma0-2-eq-zero.md)

## Expansion

Assemble irreducibility and modularity to get a nonzero level-two form, contradicting its vanishing.

## Conventions

For the input carrier and the integral-to-rational comparison, see [Frey packages and their models](../trace-modularity-and-lifting/normalized-fermat-solutions-and-frey-curves.md).

## Sources

- Anthropic, [FreyPackage.no_frey_package](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_FreyPackage_no_frey_package.lean#L129).
- Anthropic, [the proof route](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md).
