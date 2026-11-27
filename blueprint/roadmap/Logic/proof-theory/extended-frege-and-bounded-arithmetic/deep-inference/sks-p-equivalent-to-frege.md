# Deep inference and Frege systems are p-equivalent

The deep-inference systems SKS and SKSg and Frege systems polynomially simulate each other: Frege derivations translate into SKSg derivations with quadratic size growth, and SKSg derivations translate back into Frege derivations of polynomial size.

**Theorem (Bruscoli–Guglielmi).**

1. For every Frege derivation $\Upsilon$ with premises $\alpha_1,\dots,\alpha_h$ ($h\ge0$) and conclusion $\beta$ there is an SKSg derivation from $\alpha_1\wedge\dots\wedge\alpha_h$ to $\beta$ of length $O(l)$ and size $O(n^2)$, where $l$ and $n$ are the length and size of $\Upsilon$. Hence SKSg and SKS p-simulate Frege.
2. For every SKSg derivation of size $n$ from $\alpha$ to $\beta$ there is a Frege derivation with premise $\alpha$ and conclusion $\beta$ of length $O(n^4)$ and size $O(n^5)$. Hence Frege p-simulates SKSg and SKS.

Here Frege is a fixed Frege system (Buss's axiom schemes extended by four axioms for the units, with modus ponens); by the Cook–Reckhow robustness theorem every Frege system in the same language is p-equivalent to it.

## Expansion

From Frege to SKSg: each axiom scheme has a fixed SKSg proof, which can be instantiated by substitution, and modus ponens is simulated by the cut rule $\mathsf i{\uparrow}$. From SKSg to Frege, two difficulties arise: deep inference applies rules inside contexts, handled by Frege derivations from $\alpha\to\beta$ to $\xi\{\alpha\}\to\xi\{\beta\}$ of size quadratic in the context (Lemma 4.8), and the equality rule hides a lot of reasoning, handled by Frege derivations for each equality step (Lemma 4.9); each rule instance of SKSg then has a short Frege derivation (Lemma 4.10). The simulations work because both systems are implicationally complete and closed under substitution, so the specific rules do not matter. SKS is reached from SKSg by the p-equivalence of SKS and SKSg.

## Depends on

- [The deep-inference system SKS in the calculus of structures](calculus-of-structures-system-sks.md)

## Proof depends on

None.

## Sources

- Paola Bruscoli and Alessio Guglielmi, "On the proof complexity of deep inference", *ACM Transactions on Computational Logic* 10(2):14, 2009, doi:10.1145/1462179.1462186, arXiv:0709.1201v3 (Section 4: Definitions 4.1 and 4.3, Theorem 4.2 (robustness), Theorem 4.6, Corollary 4.7, Lemmas 4.8 to 4.10, Theorem 4.11, Corollary 4.12, Remark 4.13).
- Sam Buss and Jakob Nordström, "Proof complexity and SAT solving", Chapter 7 of *Handbook of Satisfiability*, 2nd edition (A. Biere, M. Heule, H. van Maaren and T. Walsh, eds.), IOS Press, 2021, doi:10.3233/FAIA200990 (Section 7.9: any two Frege systems polynomially simulate each other).
