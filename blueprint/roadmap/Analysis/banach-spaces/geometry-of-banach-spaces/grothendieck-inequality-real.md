# Grothendieck's inequality (real case)

There is a constant $K > 0$ such that for all
$m, n \in \mathbb{N}$, every real $m \times n$ matrix $A = (a_{ij})$, every real Hilbert space $H$
and all vectors $x_1, \dots, x_m, y_1, \dots, y_n \in H$ of norm at most $1$, there are signs
$\varepsilon_1, \dots, \varepsilon_m, \delta_1, \dots, \delta_n \in \{1, -1\}$ such that
$\bigl|\sum_{i=1}^{m} \sum_{j=1}^{n} a_{ij} \langle x_i, y_j \rangle\bigr| \le
K \bigl|\sum_{i=1}^{m} \sum_{j=1}^{n} a_{ij} \varepsilon_i \delta_j\bigr|$.

## Sources

- A. Grothendieck, Resume de la theorie metrique des produits tensoriels topologiques, Bol. Soc. Mat. Sao Paulo 8 (1953) 1-79, inequality; Pisier, Grothendieck's theorem past and present, 2012; Lean states real finite-matrix scalarized form with `Fin`-indexed unit vectors and `±1` signs, existential universal constant `K`.
