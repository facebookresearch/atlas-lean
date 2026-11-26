# No cofixed quotient for Frey exponents five, seven, or thirteen

If a Frey package has exponent $p=5$, $p=7$, or $p=13$, there is no Galois-stable proper nonzero submodule of its $p$-torsion on whose quotient every element of $\Gamma_{\mathbb Q}$ acts trivially.

## Depends on

- [Frey torsion and the cofixed predicate](frey-torsion-and-cofixed-lines.md)

## Proof depends on

- [Fermat’s equation at seven](../../../../NumberTheory/diophantine-equations/higher-degree-equations/fermat-prime-exponents/fermat-equation-at-exponent-7.md)
- [Fermat’s equation at thirteen](../../../../NumberTheory/diophantine-equations/higher-degree-equations/fermat-prime-exponents/fermat-equation-at-exponent-13.md)

## Expansion

Apply Fermat’s theorem at each indicated exponent, converting the nonzero-integer equation to the natural-number formulation. At exponent five use the [proved exponent-five case](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/NumberTheory/FLT/Five.lean#L1759-L1762). In each case the Fermat equation rules out the package itself.

## Conventions

For the input carrier and the integral-to-rational comparison, see [Frey packages and their models](../trace-modularity-and-lifting/normalized-fermat-solutions-and-frey-curves.md).

## Sources

- Anthropic, [FreyPackage.frey_no_cofixed_small](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_FreyPackage_frey_no_cofixed_small.lean#L13).
- Anthropic, [the proof route](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md).
- Anthropic, [the separate contradictions at exponents five, seven, and thirteen](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_small.lean#L16-L29).
