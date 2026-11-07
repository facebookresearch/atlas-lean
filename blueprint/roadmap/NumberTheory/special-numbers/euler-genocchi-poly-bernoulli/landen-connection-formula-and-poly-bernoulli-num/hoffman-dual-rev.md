# Hoffman dual on reversed lists

The auxiliary map $R$ on finite lists
$l = (l_1, \dots, l_m)$ of natural numbers is defined recursively by: $R(()) = ()$; $R(l) = ()$
if $l_1 = 0$; $R((1)) = (1)$; if $l_1 = 1$ and $m \ge 2$, then $R(l)$ is $R((l_2, \dots, l_m))$
with its first entry increased by $1$ (unchanged if that list is empty); and if $l_1 \ge 2$, then
$R(l) = (1, r_1, \dots, r_p)$ where $(r_1, \dots, r_p) = R((l_1 - 1, l_2, \dots, l_m))$.

Reading an index from its last entry, these are the rules $(1)^\vee = (1)$,
$(k\rightarrow)^\vee = (k^\vee)\uparrow$ and $(k\uparrow)^\vee = (k^\vee)\rightarrow$ of Hoffman's
dual index, where $k\uparrow$ increases the last entry of $k$ by $1$ and $k\rightarrow$ appends an
entry $1$: the Hoffman dual of an index $k$ is the reverse of $R$ applied to the reverse of $k$.

## Sources

- Ken Kamano, *A Generalization of the Landen Connection Formula and Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2, definition of Hoffman's dual index.
