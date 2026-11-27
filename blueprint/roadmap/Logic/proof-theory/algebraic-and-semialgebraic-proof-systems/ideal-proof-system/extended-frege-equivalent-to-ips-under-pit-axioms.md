# Extended Frege is p-equivalent to IPS if PIT axioms are EF-provable

If some family of polynomial-size Boolean circuits for polynomial identity testing has PIT axioms with polynomial-size Extended Frege proofs, then Extended Frege and the Ideal Proof System are polynomially equivalent; the same scaling holds for $\mathcal{C}$-Frege, which ties $\mathrm{AC}^0[p]$-Frege lower bounds to algebraic circuit lower bounds.

Fix a standard Boolean encoding $[C]$ of constant-free algebraic circuits, of size polynomial in the circuit size. Let $K = \{K_{m,n}\}$ be Boolean circuits that take the encoding of a size-$m$ constant-free algebraic circuit $C$ over $x_1, \dots, x_n$ and, when $C$ has polynomial degree, output $1$ exactly when $C$ computes the zero polynomial. The **PIT axioms** for $K$ are the propositional formulas, with propositional variables encoding the circuits involved and Boolean variables $\vec{p}$:

1. $K([C(\vec{x})]) \rightarrow K([C(\vec{p})])$ (a zero polynomial vanishes on Boolean inputs);
2. $K([C(\vec{x})]) \rightarrow \neg K([1 - C(\vec{x})])$;
3. $K([G(\vec{x})]) \wedge K([C(\vec{x}, 0)]) \rightarrow K([C(\vec{x}, G(\vec{x}))])$ (a circuit computing $0$ may be substituted for the constant $0$);
4. $K([C(\vec{x})]) \rightarrow K([C(\pi(\vec{x}))])$ for permutations $\pi$ of the variables.

**Theorem.** If there is a family $K$ of polynomial-size Boolean circuits computing PIT such that the PIT axioms for $K$ have polynomial-size Extended Frege proofs, then Extended Frege is polynomially equivalent to IPS.

**Scaled-down version.** Let $\mathcal{C}$ be any class of circuits closed under $\mathrm{AC}^0$ circuit reductions. If there is a family $K$ of polynomial-size Boolean circuits computing PIT (not necessarily in $\mathcal{C}$) whose PIT axioms have polynomial-size $\mathcal{C}$-Frege proofs, then $\mathcal{C}$-Frege is polynomially equivalent to IPS, and consequently to Extended Frege.

**Corollary.** For any $d$: if some family of tautologies has no polynomial-size $\mathrm{AC}^0[p]$-Frege proofs and $\mathrm{AC}^0[p]$-Frege has polynomial-size proofs of the (depth-$d$) PIT axioms for some $K$, then $\mathrm{VNP}_{\mathbb{F}_p}$ does not have polynomial-size (depth-$d$) algebraic circuits.

## Proof sketch

IPS verification is randomized, so the usual equivalence between simulating a system and proving its soundness is adapted: using $K$ one builds a polynomial-size Boolean circuit $\mathrm{Proof}_{\mathrm{IPS}}([C], [\varphi])$ that checks $K([C(\vec{x}, \vec{0})])$ and $K([1 - C(\vec{x}, \vec{Q}^{\varphi}(\vec{x}))])$ for the polynomial translation $\vec{Q}^{\varphi}$ of a 3CNF $\varphi$. Efficient EF proofs of the propositional soundness statement for IPS give the simulation, and these soundness proofs follow from efficient EF proofs of the four PIT axioms. Since IPS p-simulates Extended Frege unconditionally, the simulation in the other direction gives equivalence. The corollary combines the scaled-down theorem with the fact that IPS lower bounds give $\mathrm{VP} \ne \mathrm{VNP}$.

## Depends on

- [Ideal Proof System](ideal-proof-system.md)

## Proof depends on

- [IPS simulates Frege, Extended Frege and bounded-depth Frege with modular gates](ips-simulates-frege-systems.md)
- [IPS lower bounds imply VP ≠ VNP](ips-lower-bounds-imply-vp-neq-vnp.md)

## Sources

- Joshua A. Grochow, Toniann Pitassi, "Circuit complexity, proof complexity, and polynomial identity testing: the Ideal Proof System", *Journal of the ACM* 65(6), 2018, https://doi.org/10.1145/3230742; numbering of arXiv:1404.3820v1 (Definition 1.7, Corollary 1.8, Theorems 4.1 and 4.5, Section 4.1).
