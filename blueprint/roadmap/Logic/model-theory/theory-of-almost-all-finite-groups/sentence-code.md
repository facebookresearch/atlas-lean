# Prenex CNF codes for sentences of group theory

A first-order sentence of the language of groups in prenex conjunctive normal form is coded by a pair $(q, m)$:

- a quantifier prefix $q = (q_0, \dots, q_{d-1})$ of booleans, where $q_j = \mathrm{true}$ stands for $\forall x_j$ and $q_j = \mathrm{false}$ for $\exists x_j$, binding $x_0, x_1, \dots, x_{d-1}$ in order;
- a matrix $m$, a finite list of clauses, each a finite list of literals $(b, w)$ with $w$ a group word in $x_0, x_1, \dots$; the literal $(\mathrm{true}, w)$ stands for $w = 1$ and $(\mathrm{false}, w)$ for $w \ne 1$.

The code denotes the sentence $Q_0 x_0 \cdots Q_{d-1} x_{d-1}\ \bigwedge_{c \in m} \bigvee_{(b, w) \in c} \lambda_{b,w}$, where $\lambda_{b,w}$ is $w = 1$ or $w \ne 1$ as above.
