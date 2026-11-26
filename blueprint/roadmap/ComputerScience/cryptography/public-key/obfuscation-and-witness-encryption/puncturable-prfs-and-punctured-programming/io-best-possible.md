# Indistinguishability obfuscation is best-possible obfuscation

For efficient (computationally) indistinguishability obfuscators, the following holds: for every efficient obfuscator $\mathcal{O}'$ (with polynomial blow-up) and every efficient learner $L$ extracting information from $\mathcal{O}'(C)$, there is an efficient simulator that, given an iO-obfuscation of $C$, produces output indistinguishable from $L(\mathcal{O}'(C))$. Hence an indistinguishability obfuscation of $C$ leaks no more about $C$ than any other efficient obfuscation of $C$ of comparable size.

## Proof sketch

Given $\mathcal{O}(C)$, the simulator computes $\mathcal{O}(\mathcal{O}'(C))$-like objects: since $\mathcal{O}'(C)$ and $C$ compute the same function, $\mathcal{O}(C)\approx\mathcal{O}(\mathcal{O}'(C))$ after padding, and from the latter the learner's view on $\mathcal{O}'(C)$ can be emulated by applying $\mathcal{O}$ to the padded circuit, so the views are indistinguishable.

## Depends on

- [Indistinguishability and virtual black-box obfuscation](../../../program-obfuscation/indistinguishability-and-virtual-black-box.md)

## Proof depends on

- [Indistinguishability and virtual black-box obfuscation](../../../program-obfuscation/indistinguishability-and-virtual-black-box.md)

## Sources

- Shafi Goldwasser, Guy N. Rothblum, "On Best-Possible Obfuscation", TCC (2007).
