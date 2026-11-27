# Indistinguishability obfuscation is best-possible obfuscation

An obfuscator $\mathcal{O}$ for a circuit family $\mathcal{C}$ (preserving functionality, with polynomial slowdown) is *(computationally) best-possible* if for every polynomial-size learner $L$ there is a polynomial-size simulator $S$ such that, for all large enough input lengths $n$ and all $C_1,C_2\in\mathcal{C}_n$ that compute the same function and satisfy $|C_1|=|C_2|$, the distributions $L(\mathcal{O}(C_1))$ and $S(C_2)$ are computationally indistinguishable. The simulator receives the *alternative* representation $C_2$ and must reproduce what the learner extracts from the obfuscation of $C_1$. Every efficient (computational) indistinguishability obfuscator is an efficient best-possible obfuscator, and conversely every best-possible obfuscator is an indistinguishability obfuscator. Hence anything efficiently computable from $\mathsf{iO}(C_1)$ is also efficiently computable from any equivalent circuit of the same size. The converse does not hold: an alternative representation, such as $C_1$ itself, can disclose information that is not available from $\mathsf{iO}(C_1)$.

## Proof sketch

Given a learner $L$, let the simulator on input $C_2$ compute $\mathsf{iO}(C_2)$ and run $L$ on it; this is efficient because $\mathsf{iO}$ is. Since $C_1$ and $C_2$ have the same size and functionality, $\mathsf{iO}(C_1)\approx\mathsf{iO}(C_2)$, so $L(\mathsf{iO}(C_1))\approx L(\mathsf{iO}(C_2))=S(C_2)$. Efficiency of the obfuscator is essential: otherwise the simulator would not be polynomial size. For the converse, apply the definition to the learner that outputs its input: both $\mathcal{O}(C_1)$ and $\mathcal{O}(C_2)$ are then close to $S(C_2)$.

## Depends on

- [Indistinguishability and virtual black-box obfuscation](../../../program-obfuscation/indistinguishability-and-virtual-black-box.md)

## Sources

- Shafi Goldwasser, Guy N. Rothblum, "On Best-Possible Obfuscation", TCC (2007), Definition 2.5, Propositions 3.4 and 3.5.
