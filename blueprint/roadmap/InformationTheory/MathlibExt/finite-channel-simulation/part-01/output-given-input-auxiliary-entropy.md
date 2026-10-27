---
declaration: def
origin: cited
statement: formalized
lean: InformationTheory.FiniteExtension.outputGivenInputAuxiliaryEntropy
---

# Output Given Input Auxiliary Entropy

Conditional entropy `H(Y | X, S)` of the output given the input and
auxiliary in an extension: `H(X, Y, S) - H(X, S)`. It vanishes exactly
when `Y` is recoverable from `(X, S)` (a deterministic function of the
pair, almost surely).

## Depends on

- [Finite Extension](finite-extension.md)
- [Finite Joint Law](finite-joint-law.md)

## Proof depends on

- [Input Auxiliary Law](input-auxiliary-law.md)
- [Shannon Entropy](../../finite-entropy/shannon-entropy.md)

## Sources

- [MathlibExt, MathlibExt.InformationTheory.FiniteChannelSimulation](../../../../../sources/v2/MathlibExt.md)
