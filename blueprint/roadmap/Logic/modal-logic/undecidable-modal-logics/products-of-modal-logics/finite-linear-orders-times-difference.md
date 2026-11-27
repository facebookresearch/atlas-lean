# Satisfiability over finite linear orders times difference frames is undecidable

Bimodal satisfiability over products of finite linear orders with difference frames is recursively enumerable but undecidable.

**Theorem (Hampson and Kurucz).** $\mathcal{C}_{\mathrm{lin}}^{\mathrm{fin}} \times \mathcal{C}_{\mathrm{diff}}$-satisfiability, whether a given bimodal formula is satisfied in some model based on the [product](products-of-linear-orders-and-difference-frames.md) of a finite linear order with a difference frame, is recursively enumerable but undecidable.

Consequently satisfiability of one-variable first-order linear temporal logic with counting to two is recursively enumerable but undecidable over the class of all finite linear orders, with constant or decreasing domains (Corollary 3.4 of the source). With expanding domains over finite linear orders the source shows the problem is Ackermann-hard (Theorem 5.3).

## Depends on

- [Products of linear orders and difference frames](products-of-linear-orders-and-difference-frames.md)
- [The arithmetical class $\Sigma_n$](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Undecidability reduces counter machine reachability (from a configuration with zero counters, does the machine reach a given state), which is $\Sigma^0_1$-hard by Minsky. Runs are encoded as in the $\Sigma^1_1$-hardness proof for $\langle\omega, <\rangle \times$ difference frames, now along a finite staircase ending at a point where the target state holds. Recursive enumerability follows from a finite product model property: a formula satisfied in the product of a finite linear order with some, possibly infinite, difference frame is already satisfied in a product with a finite difference frame, obtained by closing a finite set of points under witnesses for the $\Diamond_1$-subformulas, so one can enumerate finite products and check them.

## Sources

- C. Hampson and A. Kurucz, "Undecidable propositional bimodal logics and one-variable first-order linear temporal logics with counting", *ACM Transactions on Computational Logic* 16(3):1–36, 2015, doi:10.1145/2757285; read as arXiv:1407.1386v3, <https://arxiv.org/abs/1407.1386v3>: Theorem 3.2 of arXiv:1407.1386v3 and its proof in Section 3, with the finite product model claim in its proof, Corollary 3.4 and Theorem 5.3.
