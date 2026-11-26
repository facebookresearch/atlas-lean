# Krajíček's R(CP): resolution over linear inequalities

In the proof system $\mathrm{R(CP)}$, lines are disjunctions $\bigvee_{i} (a_i \cdot x \ge b_i)$ of integer linear inequalities. The rules are: weakening by adding disjuncts; the cutting-planes rules (addition, positive scaling, and Chvátal-Gomory rounding $\frac{a}{c} \cdot x \ge \lceil b/c \rceil$ when $c$ divides all coefficients of $a$) applied to one disjunct in the presence of a common side disjunction; the **integer cut** that derives $(a \cdot x \ge b) \vee (a \cdot x \le b - 1)$; and resolution that removes a contradictory pair of disjuncts. A refutation derives the empty disjunction. **Tree-like** $\mathrm{R(CP)}$ restricts proofs to trees.

## Depends on

- [The stabbing planes proof system](stabbing-planes-system.md)

## Sources

- J. Krajíček, "Discretely ordered modules as a first-order extension of the cutting planes proof system", Journal of Symbolic Logic 63 (1998) 1582-1596.
- P. Beame, N. Fleming, R. Impagliazzo, A. Kolokolova, D. Pankratov, T. Pitassi, R. Robere, "Stabbing planes", ITCS (2018), arXiv:1710.03219.
