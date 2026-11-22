# Gotoh table row from the previous row

For a letter $a$, a sequence $y$ and a previous row $P = (P_0, P_1, \dots)$ of triples (a missing entry read as $(0, 0, 0)$), the next row is: for empty $y$, the single triple obtained by the [empty-suffix step](step-x.md) from $P_0$; for $y = b y'$, the triple obtained by the [step](step.md) from $a, b$, $d = P_1$, $u = P_0$ and $l$ the first triple of the rest, followed by the rest, where the rest is the next row for $a$, $y'$ and $(P_1, P_2, \dots)$.
