# Bus admittance matrix of a network

Let $n$ and $m$ be natural numbers (the numbers of buses and branches),
$B \in \mathbb{R}^{n \times m}$ a real matrix, $y \in \mathbb{C}^m$ branch admittances and
$y^{\mathrm{sh}} \in \mathbb{C}^n$ shunt admittances. The bus admittance matrix is the complex
$n \times n$ matrix

$$Y = B\, \mathrm{diag}(y)\, B^{\mathsf T} + \mathrm{diag}(y^{\mathrm{sh}}),$$

with entries

$$Y_{ab} = \sum_{e} B_{ae}\, y_e\, B_{be} + \delta_{ab}\, y^{\mathrm{sh}}_a.$$

Since $B$ is real, $Y$ is symmetric, $Y^{\mathsf T} = Y$; it is Hermitian exactly when all its
entries are real. It maps the node voltages to the
[nodal current injections](bus-admittance-mul-vec-eq-node-injection.md). In the physical reading $B$
is the signed node–branch incidence matrix (one entry $1$ and one entry $-1$ in each column) and the
branches and shunts are passive, with nonnegative conductances $\operatorname{Re} y_e$ and
$\operatorname{Re} y^{\mathrm{sh}}_a$; the definition allows any real $B$ and any complex
admittances.
