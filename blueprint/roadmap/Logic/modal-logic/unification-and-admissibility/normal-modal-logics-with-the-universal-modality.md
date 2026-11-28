# Normal modal logics with the universal modality

A normal modal logic with the universal modality is a set of formulas in a language with a relational box $\Box$ and a universal box $\forall$ that contains the axioms of $\mathbf{K}$ for both boxes and the S5 axioms for $\forall$, with $\forall p \to \Box p$. The least such logic is $\mathbf{K}_u$; adding $\Box p \to \Box\Box p$ gives $\mathbf{K4}_u$.

The language $\mathcal{L}$ has infinitely many propositional variables $p_0, p_1, \dots$, the Boolean connectives $\wedge, \neg$ (and the derived $\vee, \to, \bot$), and two unary modal operators $\Box$ and $\forall$, with duals $\Diamond = \neg\Box\neg$ and $\exists = \neg\forall\neg$.

A *normal modal logic with the universal modality* is a set $L$ of $\mathcal{L}$-formulas that contains all propositional tautologies and the axioms

$$
\Box(p \to q) \to (\Box p \to \Box q), \quad \forall(p \to q) \to (\forall p \to \forall q), \quad \forall p \to p, \quad \forall p \to \forall\forall p, \quad p \to \forall\exists p, \quad \forall p \to \Box p,
$$

and is closed under modus ponens, the necessitation rules $\varphi / \Box\varphi$ and $\varphi / \forall\varphi$, and uniform substitution. $\mathbf{K}_u$ is the smallest such logic and $\mathbf{K4}_u$ is the smallest one containing $\Box p \to \Box\Box p$. A logic $L$ lies *between* $\mathbf{K}_u$ and $\mathbf{K4}_u$ when $\mathbf{K}_u \subseteq L \subseteq \mathbf{K4}_u$.

**Semantics.** A frame is a directed graph $\mathfrak{F} = (W, R)$ and a model adds a valuation $\mathfrak{V}$ sending each variable to a subset of $W$. Truth of $\Box\psi$ at $x$ means truth of $\psi$ at every $y$ with $x R y$; truth of $\forall\psi$ at $x$ means truth of $\psi$ at every $y \in W$. A formula is valid in a frame when it is true at every point of every model on that frame. $\mathbf{K}_u$ is the set of formulas valid in all frames and $\mathbf{K4}_u$ the set of formulas valid in all transitive frames; satisfiability is EXPTIME-complete for $\mathbf{K}_u$ and PSPACE-complete for $\mathbf{K4}_u$ (Fact 2.1 of the source, recalled from Areces, Blackburn and Marx).

## Depends on

- [Kripke model](../kripke-semantics/kripke-model.md)
- [Theorems of a normal modal logic](../normal-modal-logics/derivable.md)

## Proof depends on

None.

## Expansion

The source states the frame characterizations as well known (Fact 2.1, citing Areces, Blackburn and Marx) and gives no proof; the standard canonical-model argument runs as follows: in the canonical model the relation for $\forall$ is an equivalence relation containing the relation for $\Box$, so restricting to one of its classes gives a model in which $\forall$ is interpreted by the total relation, and transitivity of the $\Box$-relation is inherited from the axiom $\Box p \to \Box\Box p$.

## Sources

- F. Wolter and M. Zakharyaschev, "Undecidability of the unification and admissibility problems for modal and description logics", *ACM Transactions on Computational Logic* 9(4):1–20, 2008, doi:10.1145/1380572.1380574; read as arXiv:cs/0609052v1, <https://arxiv.org/abs/cs/0609052v1>: Section 2, the definitions of $\mathcal{L}$, $\mathbf{K}_u$ and $\mathbf{K4}_u$, Fact 2.1 and Definition 2.2.
