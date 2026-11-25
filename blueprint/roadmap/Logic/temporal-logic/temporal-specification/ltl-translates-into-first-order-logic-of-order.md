# LTL translates into first-order logic of order

For every LTL formula $\varphi$ over a finite set of atomic propositions there is a formula $\varphi^*(x)$ of $\mathrm{FO}[<]$ with one free variable such that for every $\omega$-word $w$ and position $k$, $w, k \models \varphi$ if and only if $w \models \varphi^*(k)$. The translation is compositional; for instance $(\varphi\, \mathbf{U}\, \psi)^*(x) = \exists y\, (x \le y \wedge \psi^*(y) \wedge \forall z\, (x \le z < y \to \varphi^*(z)))$. Kamp's theorem gives the converse for temporal logic with both the future operator until and the past operator since: over $(\mathbb{N}, <)$, every $\mathrm{FO}[<]$ formula with one free variable is equivalent to such a temporal formula. For formulas evaluated at the initial position, future operators suffice (Gabbay, Pnueli, Shelah and Stavi).

## Depends on

- [First-order logic of order over infinite words](first-order-logic-of-order-over-infinite-words.md)
- [Satisfaction of LTL formulas on ω-words](../linear-temporal-logic/satisfies.md)

## Sources

- J. A. W. Kamp, *Tense Logic and the Theory of Linear Order*, PhD thesis, University of California, Los Angeles, 1968
- A. Rabinovich, "A proof of Kamp's theorem", *Logical Methods in Computer Science* 10(1):14, 2014, Sections 2.1–2.3 and Theorem 2.1, <https://arxiv.org/abs/1401.2580>
- D. Gabbay, A. Pnueli, S. Shelah and J. Stavi, "On the temporal analysis of fairness", *Proceedings of the 7th ACM POPL*, 1980
