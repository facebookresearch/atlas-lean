# IPS lower bounds imply VP ≠ VNP

A super-polynomial lower bound on Hilbert-like IPS proofs of any family of tautologies implies that $\mathrm{VNP} \ne \mathrm{VP}$, because every CNF tautology already has Hilbert-like IPS certificates in $\mathrm{VNP}$; lower bounds on the number of lines of Polynomial Calculus proofs imply the permanent versus determinant conjecture.

**Theorem.** For any ring $R$:

1. a super-polynomial lower bound on (constant-free) Hilbert-like $\mathrm{IPS}_R$ proofs of any family of tautologies implies $\mathrm{VNP}_R \ne \mathrm{VP}_R$ (respectively $\mathrm{VNP}^0_R \ne \mathrm{VP}^0_R$);
2. a super-polynomial lower bound on the number of lines in Polynomial Calculus proofs implies the permanent versus determinant conjecture $\mathrm{VNP} \ne \mathrm{VP}_{ws}$.

**Key lemma.** Every family of CNF tautologies $(\varphi_n)$ has a Hilbert-like family of IPS certificates $(C_n)$ in $\mathrm{VNP}^0_R$.

Together with the fact that polynomial-size constant-free IPS proofs of all tautologies over any field would give $\mathrm{NP} \subseteq \mathrm{coMA}$ (Merlin guesses the proof, Arthur checks both defining identities by randomized PIT), this yields: if $\mathrm{NP} \not\subseteq \mathrm{coMA}$, then $\mathrm{VNP}^0_R \ne \mathrm{VP}^0_R$ for every ring $R$.

## Proof sketch

Write the unsatisfiable CNF as $\kappa_1 \wedge \dots \wedge \kappa_m$ and translate $\kappa_i$ to the product $C_i(\vec{x})$ of factors $b(f, x) = fx + (1-f)(1-x)$, so $C_i(\vec{e}) = 1$ exactly when $\vec{e}$ falsifies $\kappa_i$. Start from the identity

$$
1 = \sum_{\vec{e} \in \{0,1\}^n} \prod_{i=1}^{n} b(e_i, x_i)
$$

and partition $\{0,1\}^n$ greedily: $A_i$ is the set of assignments falsifying $\kappa_i$ and satisfying $\kappa_j$ for all $j < i$. Since $C_i$ divides every term indexed by $\vec{e} \in A_i$, the identity becomes the Hilbert-like certificate

$$
\sum_{\vec{e} \in \{0,1\}^n} \sum_{i=1}^{m} y_i \, C_i(\vec{e}) \Big( \prod_{j < i} (1 - C_j(\vec{e})) \Big) \prod_{j \,:\, x_j \notin \kappa_i} b(e_j, x_j),
$$

whose summand is a polynomial-size constant-depth formula using only the constants $0, 1, -1$, so the certificate lies in $\mathrm{VNP}^0$. If $\mathrm{VP} = \mathrm{VNP}$ these certificates would have polynomial-size circuits, contradicting the assumed lower bound. The Polynomial Calculus statement uses the equivalence between the number of lines and Hilbert-like IPS over weakly skew circuits.

## Depends on

- [Linear and circuit-restricted Ideal Proof Systems](linear-and-restricted-ideal-proof-systems.md)
- [Polynomial calculus](../polynomial-calculus.md)
- [CNF formula](../../../propositional-logic/conjunctive-normal-form/cnf.md)
- [The complexity class NP](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/np.md)
- [The class MA (Merlin–Arthur)](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/ma.md)
- [The class coMA](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/co-ma.md)

## Proof depends on

- [Polynomial calculus line count is p-equivalent to Hilbert-like determinantal IPS](pc-line-count-equivalent-to-hilbert-like-determinantal-ips.md)

## Sources

- Joshua A. Grochow, Toniann Pitassi, "Circuit complexity, proof complexity, and polynomial identity testing: the Ideal Proof System", *Journal of the ACM* 65(6), 2018, https://doi.org/10.1145/3230742; numbering of arXiv:1404.3820v1 (Theorem 3.1, Lemma 3.2, Proposition 1.4, Corollary 1.6, Proposition 2.2).
