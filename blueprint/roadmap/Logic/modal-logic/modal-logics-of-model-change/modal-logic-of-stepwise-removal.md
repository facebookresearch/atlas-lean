# Modal logic of stepwise removal

The modal logic of stepwise removal MLSR adds to the basic modal language a binary modality $\langle -\varphi\rangle\psi$, true at a point $s$ when some point $t \neq s$ satisfying $\varphi$ can be deleted from the model so that $\psi$ is true at $s$ in what remains.

**Syntax.** Formulas are given by

$$
\varphi ::= p \mid \neg\varphi \mid (\varphi \vee \varphi) \mid \Diamond\varphi \mid \langle -\varphi\rangle\varphi
$$

with $p$ a proposition letter; $\Box$ and $[-\varphi]$ are the duals. The multimodal version has one diamond $\Diamond_i$ for each of several accessibility relations $R_i$.

**Semantics.** Formulas are evaluated at points of relational models $\mathcal{M} = (W, R, V)$ (or $(W, (R_i)_i, V)$), with the usual clauses for atoms, Booleans and $\Diamond$, and

$$
\mathcal{M}, s \models \langle -\varphi\rangle\psi \iff \text{there is } t \neq s \text{ in } W \text{ with } \mathcal{M}, t \models \varphi \text{ and } \mathcal{M} - \{t\}, s \models \psi,
$$

where $\mathcal{M} - \{t\}$ is the submodel with domain $W \setminus \{t\}$. A formula is satisfiable when it is true at some point of some model.

## Depends on

- [Kripke model](../kripke-semantics/kripke-model.md)
- [Modal formulas](../kripke-semantics/formula.md)
- [Satisfaction in a Kripke model](../kripke-semantics/satisfies.md)

## Proof depends on

None.

## Expansion

The modality defines the difference modality $\mathsf{D}\varphi = \langle -\varphi\rangle\top$ and hence the universal modality, and iterating $\langle -\top\rangle$ counts finite cardinalities. MLSR lies inside first-order logic with equality via a translation that keeps track of the finitely many deleted points, so its validities are recursively enumerable; the source gives a complete axiomatization in a language extended with nominals and relativization, and shows model checking is PSPACE-complete.

## Sources

- J. van Benthem, K. Mierzewski and F. Zaffora Blando, "The modal logic of stepwise removal", *The Review of Symbolic Logic* 15(1):36–63, 2022, doi:10.1017/S1755020320000258; read as arXiv:2103.05117v1, <https://arxiv.org/abs/2103.05117v1>: Definitions 1.1 and 2.1 (semantics and syntax of MLSR), the definability of $\mathsf{D}$ in Section 2, and Theorems 4.1 and 5.1.
