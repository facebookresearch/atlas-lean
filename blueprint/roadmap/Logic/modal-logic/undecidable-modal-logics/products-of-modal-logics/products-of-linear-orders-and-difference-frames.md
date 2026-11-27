# Products of linear orders and difference frames

The product of a frame $(T, <)$ and a difference frame $(W, \neq)$ is the 2-frame on $T \times W$ whose first relation moves along $<$ in the first coordinate and whose second relation moves to any different point in the second coordinate; bimodal formulas with $\Diamond_0$, $\Diamond_1$ are interpreted on it.

**Bimodal formulas** are $\phi ::= p \mid \neg\phi \mid \phi \wedge \phi \mid \Diamond_0\phi \mid \Diamond_1\phi$. A *2-frame* $\langle W, R_0, R_1\rangle$ interprets $\Diamond_i$ by $R_i$ in the usual Kripke way, and a formula is *satisfied* in a model if it is true at some point.

**Products.** For frames $\mathfrak{F}_0 = (W_0, R_0)$ and $\mathfrak{F}_1 = (W_1, R_1)$ the *product* $\mathfrak{F}_0 \times \mathfrak{F}_1$ is the 2-frame on $W_0 \times W_1$ with $(u, v) \bar{R}_0 (u', v')$ iff $u R_0 u'$ and $v = v'$, and $(u, v) \bar{R}_1 (u', v')$ iff $v R_1 v'$ and $u = u'$. For classes $\mathcal{C}_0$, $\mathcal{C}_1$ of frames, $\mathcal{C}_0 \times \mathcal{C}_1$ is the class of products of members, and *$\mathcal{C}_0 \times \mathcal{C}_1$-satisfiability* asks whether a given bimodal formula is satisfied in some model based on a frame of $\mathcal{C}_0 \times \mathcal{C}_1$.

**Classes used.** A *linear order* is an irreflexive, transitive and trichotomous relation; $\mathcal{C}_{\mathrm{lin}}^{\mathrm{fin}}$ is the class of finite linear orders and $\langle\omega, <\rangle$ the natural numbers. A *difference frame* is $(W, \neq)$ for a nonempty set $W$, and $\mathcal{C}_{\mathrm{diff}}$ is the class of all difference frames; $\mathbf{Diff}$ is its logic. On a product with a difference frame, $\Diamond_1^+\phi = \phi \vee \Diamond_1\phi$ is the universal modality along the second coordinate.

## Depends on

- [Kripke model](../../kripke-semantics/kripke-model.md)
- [Partially ordered set](../../../../Order/ordered-sets/partial-order.md)
- [Modal formulas](../../kripke-semantics/formula.md)

## Proof depends on

None.

## Expansion

Products with difference frames are the bimodal counterpart of one-variable first-order linear temporal logic with the counting quantifier "there are at least two": the time coordinate is the linear order and the second coordinate is the first-order domain, constant along time. If both component classes are recursively first-order definable, product satisfiability is co-r.e. (Theorem 2.1 of the source, from Gabbay, Kurucz, Wolter and Zakharyaschev).

## Sources

- C. Hampson and A. Kurucz, "Undecidable propositional bimodal logics and one-variable first-order linear temporal logics with counting", *ACM Transactions on Computational Logic* 16(3):1–36, 2015, doi:10.1145/2757285; read as arXiv:1407.1386v3, <https://arxiv.org/abs/1407.1386v3>: Section 2 (bimodal formulas, 2-frames, products, linear orders, difference frames and the connection with one-variable first-order temporal logic with counting) and Theorem 2.1.
