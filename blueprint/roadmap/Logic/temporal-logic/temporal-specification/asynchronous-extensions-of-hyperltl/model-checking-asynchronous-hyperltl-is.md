# Model checking asynchronous HyperLTL is equivalent to second-order arithmetic

Model checking finite transition systems against asynchronous HyperLTL sentences is exactly as hard as deciding truth in second-order arithmetic, already for each of the two fragments with an existential or a universal trajectory quantifier.

**Theorem (Regaud and Zimmermann).** Model checking [asynchronous HyperLTL](asynchronous-hyperltl.md), deciding $\mathcal T \models \varphi$ for a finite transition system $\mathcal T$ and a sentence $\varphi$, is equivalent to truth in second-order arithmetic $(\mathbb N, +, \cdot, <, \in)$: there are reductions in both directions, and the lower bound holds for A-AHLTL and for E-AHLTL (Theorem 4 of the source); the proof reduces to model checking a fixed transition system. The same holds for finite-state satisfiability, whether some transition system satisfies a given sentence (Theorem 5).

## Depends on

- [Asynchronous HyperLTL](asynchronous-hyperltl.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

*Upper bound.* A polynomial-time translation maps a pair $(\mathcal T, \varphi)$ to a sentence of second-order arithmetic: a trace $\sigma$ is coded by the set $\{\langle i, p\rangle \mid p \in \sigma(i)\}$ through Cantor's pairing function, a formula $\alpha_{\mathrm{trc}}$ checks that a set codes a trace of $\mathcal T$, and trace quantifiers, pointer assignments and trajectories become set quantifiers. For finite-state satisfiability one also quantifies over a code of a finite transition system.

*Lower bound.* A polynomial-time translation maps sentences of second-order arithmetic to pairs of a fixed transition system and an A-AHLTL sentence. A trace encodes the set $\{n \mid \# \in \sigma(n)\}$, and numbers are encoded by traces encoding singletons, so trace quantifiers mimic first- and second-order quantifiers; a further proposition implements multiplication, and a proposition $\dagger$ alternating on every trace gives access to the trajectory (Remark 2). The lower bound for E-AHLTL follows from that for A-AHLTL. For finite-state satisfiability, an A-AHLTL sentence $\alpha_m$ pins down the traces of the fixed system up to projection, so finite-state satisfiability of $\alpha_m \wedge \varphi$ is equivalent to model checking.

## Sources

- G. Regaud and M. Zimmermann, "The Complexity of Asynchronous HyperLTL", *Electronic Proceedings in Theoretical Computer Science* 454, 2026, pp. 183–199, <https://doi.org/10.4204/EPTCS.454.13>; read as arXiv:2606.06091v2, <https://arxiv.org/abs/2606.06091v2>: Section 2 (arithmetic and the analytical hierarchy), Theorems 4 and 5 with their proofs, and Section 1.
