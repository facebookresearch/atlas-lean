# Positive relevant logics and Routley–Meyer frames

Positive relevant logics are sets of formulas in $\wedge$, $\vee$, $\to$ closed under modus ponens and adjunction; the weakest one considered here, $\mathsf{TWJ}^+$, adds hypothetical syllogism, prefixing and suffixing to the basic logic $\mathsf{B}^+$. They are interpreted on Routley–Meyer frames, and the semilattice logic $\mathsf{S}$ on join-semilattices.

**Language.** Formulas are $\varphi ::= p \mid \varphi \wedge \varphi \mid \varphi \vee \varphi \mid \varphi \to \varphi$ with $p$ from a countable set of propositional letters; there is no negation, fusion or truth constant.

**Axiomatic logics.** $\mathsf{TWJ}^+$ is given by the axiom schemes

$$
\varphi \to \varphi, \quad \varphi \wedge \psi \to \varphi, \quad \varphi \wedge \psi \to \psi, \quad (\varphi \to \psi) \wedge (\varphi \to \chi) \to (\varphi \to \psi \wedge \chi),
$$

$$
\varphi \to \varphi \vee \psi, \quad \psi \to \varphi \vee \psi, \quad (\varphi \to \chi) \wedge (\psi \to \chi) \to (\varphi \vee \psi \to \chi), \quad \varphi \wedge (\psi \vee \chi) \to (\varphi \wedge \psi) \vee (\varphi \wedge \chi),
$$

hypothetical syllogism $(\varphi \to \psi) \wedge (\psi \to \chi) \to (\varphi \to \chi)$, prefixing $(\varphi \to \psi) \to ((\chi \to \varphi) \to (\chi \to \psi))$ and suffixing $(\varphi \to \psi) \to ((\psi \to \chi) \to (\varphi \to \chi))$, closed under modus ponens ($\varphi, \varphi \to \psi / \psi$) and adjunction ($\varphi, \psi / \varphi \wedge \psi$). Adding cumulatively pseudo-modus ponens $\varphi \wedge (\varphi \to \psi) \to \psi$, contraction $(\varphi \to (\varphi \to \psi)) \to (\varphi \to \psi)$, the E axioms and assertion $\varphi \to ((\varphi \to \psi) \to \psi)$ gives $\mathsf{C}^+ \subsetneq \mathsf{T}^+ \subsetneq \mathsf{E}^+ \subsetneq \mathsf{R}^+$, the $\{\wedge, \vee, \to\}$-fragments of the relevant logics T, E and R.

**Frames.** A Routley–Meyer frame is $(K, \cdot, N)$ with $\cdot : K \times K \to \mathcal{P}(K)$ and $N \subseteq K$, such that the relation $x \leq y$ iff $y \in N \cdot x$ is reflexive and transitive, $N$ is upward closed, and $z \in x \cdot y$ with $x' \leq x$, $y' \leq y$, $z \leq z'$ gives $z' \in x' \cdot y'$. Valuations assign upsets to letters; $\wedge$ and $\vee$ are pointwise, and $x \Vdash \varphi \to \psi$ iff for all $y, z$ with $y \Vdash \varphi$ and $z \in x \cdot y$ we have $z \Vdash \psi$. A formula is valid in a frame if it is true at every normal point $n \in N$ under every valuation, and $\mathrm{Log}(\mathcal{C})$ is the set of formulas valid in every frame of a class $\mathcal{C}$. $\mathsf{TWJ}^+$ is sound and complete for the frames satisfying $x \cdot y \subseteq x \cdot (x \cdot y)$, $(x \cdot y) \cdot z \subseteq x \cdot (y \cdot z)$ and $(x \cdot y) \cdot z \subseteq y \cdot (x \cdot z)$.

**Semilattice logic.** A semilattice frame $(S, \sqcup, 0)$ is a join-semilattice with least element $0$, read as the Routley–Meyer frame with $x \cdot y = \{x \sqcup y\}$ and $N = \{0\}$; thus $x \Vdash \varphi \to \psi$ iff $x \sqcup y \Vdash \psi$ for every $y \Vdash \varphi$, and validity means truth at $0$ under every valuation (valuations are arbitrary subsets here). $\mathsf{S}$ is the set of formulas valid in all semilattice frames, and $\mathrm{Log}(\mathcal{P}_{\mathrm{fin}}(\mathbb{N}), \cup, \varnothing)$ is the logic of the single semilattice frame of finite sets of natural numbers under union. One has $\mathsf{R}^+ \subseteq \mathsf{SetFr} \subseteq \mathsf{S} \subseteq \mathrm{Log}(\mathcal{P}_{\mathrm{fin}}(\mathbb{N}), \cup, \varnothing)$, where $\mathsf{SetFr}$ is the logic of Routley–Meyer set frames, the $\mathsf{R}^+$-frames with $x \cdot x \subseteq N \cdot x$.

## Depends on

None.

## Proof depends on

None.

## Expansion

Urquhart's semilattice semantics reads $x$ as a body of information and $x \sqcup y$ as its combination with $y$; the resulting logic $\mathsf{S}$ properly extends $\mathsf{R}^+$. Replacing the last three axioms of $\mathsf{TWJ}^+$ by the corresponding rules gives $\mathsf{B}^+$, and $\mathsf{TW}^+$, which has prefixing and suffixing but not hypothetical syllogism, is decidable (Giambrone).

## Sources

- S. B. Knudstorp, "Undecidability in relevant logic", *The Journal of Symbolic Logic*, 2026, pp. 1–27, doi:10.1017/jsl.2026.10277; read as arXiv:2605.29880v2, <https://arxiv.org/abs/2605.29880v2>: Section 2 (syntax, the axiomatic logics, Routley–Meyer frames and their correspondence conditions, semilattice frames, $\mathsf{S}$ and $\mathsf{SetFr}$).
