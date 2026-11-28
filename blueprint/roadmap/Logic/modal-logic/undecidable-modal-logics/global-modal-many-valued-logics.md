# Global modal many-valued logics are undecidable

Global consequence in Kripke models valued in residuated lattices such as the standard Łukasiewicz or product algebra is undecidable, already for three-variable formulas, unlike classical modal logic and the underlying propositional many-valued logics.

**Theorem (Vidal).** An *FL$_{ew}$-algebra* is a bounded commutative integral residuated lattice $(A, \wedge, \vee, \cdot, \to, 0, 1)$. It is *weakly saturated* if $a \le b^n$ for all $n \in \mathbb N$ implies $ab = a$, and *$n$-contractive* if $a^{n+1} = a^n$ for all $a$. Let $\mathsf A$ be a class of weakly saturated FL$_{ew}$-chains such that for every $n$ some member of $\mathsf A$ is not $n$-contractive; for instance $\{[0,1]_{\L}\}$ (the standard MV-algebra), $\{\mathrm{MV}_n : n \in \mathbb N\}$ or $\{[0,1]_\Pi\}$ (the standard product algebra).

Modal formulas are built from propositional variables and constants $0, 1$ by $\wedge, \vee, \cdot, \to$ and unary $\square, \lozenge$. An *$A$-Kripke model* $\langle W, R, e\rangle$ is a Kripke frame with $e : W \times \mathrm{Var} \to A$, extended by $e(v, \square\varphi) = \bigwedge_{Rvw} e(w, \varphi)$ and $e(v, \lozenge\varphi) = \bigvee_{Rvw} e(w, \varphi)$; it is *safe* if all these infima and suprema exist. For a finite set $\Gamma$ and a formula $\varphi$, $\Gamma \vdash_{\mathcal F_{\mathsf A}} \varphi$ (*global consequence* over a class $\mathcal F$ of frames) means: for every frame in $\mathcal F$, every $A \in \mathsf A$ and every safe $A$-Kripke model on that frame, if every formula of $\Gamma$ takes value $1$ at every world, so does $\varphi$. Let $\mathcal L$ be the class of frames isomorphic to finite strict chains $0 \to 1 \to \cdots \to k$ ($k \in \mathbb N$).

For every class of frames $\mathcal F \supseteq \mathcal L$, the relation $\vdash_{\mathcal F_{\mathsf A}}$ is undecidable, already restricted to formulas in three variables. In particular global consequence over all frames, $\vdash_{K\mathsf A}$, and over all finite frames, $\vdash_{\omega K\mathsf A}$, are undecidable; for instance global modal Łukasiewicz logic and global modal product logic.

The same holds over any class of transitive frames containing isomorphic copies of the finite strict linear orders $(\{0, \ldots, i\}, <)$, for instance over all transitive frames ($K4$) (Corollary 3.10 of the source). By contrast, the local consequence and the tautologies of standard Łukasiewicz modal logic are decidable.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

From an instance $P$ of the Post correspondence problem, with words coded as numbers in a base $s$, one computes a finite set $\Gamma_P$ and a formula $\varphi_P$ in the variables $x, y, z$ such that $P$ has a solution iff $\Gamma_P \nvdash_{K\mathsf A} \varphi_P$ iff $\Gamma_P \nvdash_{\omega K\mathsf A} \varphi_P$ iff $\Gamma_P \nvdash_{\mathcal L_{\mathsf A}} \varphi_P$ (Theorem 3.2). A solution is laid out along a finite chain of worlds, the truth values of $x$ and $y$ in a non-contractive algebra encoding the concatenated words through powers $a^n$ of an element with $a^{n+1} < a^n$; the formulas of $\Gamma_P$, imposed globally, force each step along the chain to append one pair of words, and weak saturation together with the finite height of the relevant worlds (Lemmas 3.3 to 3.8) turns any countermodel into a solution.

## Sources

- A. Vidal, "Undecidability and non-axiomatizability of modal many-valued logics", *The Journal of Symbolic Logic* 87(4):1576–1605, 2022, <https://doi.org/10.1017/jsl.2022.32>; numbers from arXiv:2101.08767v2, <https://arxiv.org/abs/2101.08767v2>: Section 2 (Definitions 2.1 to 2.4), Section 3: Theorem 3.1, Theorem 3.2, Lemmas 3.3 to 3.8 and Corollary 3.10.
