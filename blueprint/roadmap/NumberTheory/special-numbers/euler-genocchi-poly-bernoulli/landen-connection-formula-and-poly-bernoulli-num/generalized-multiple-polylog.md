# Kamano's generalized multiple polylogarithm

Let $g = (g_0, g_1, \dots, g_s)$ be Landen
data, where $g_0$ has rows $(1, -1)$ and $(c_0, d_0)$ and $g_i$ has rows $(a_i, b_i)$ and
$(c_i, d_i)$, and let $\beta, \gamma \in \mathbb{R}^s$. For a matrix $h$ with rows $(a, b)$ and
$(c, d)$ put $G_h(u) = \frac{c}{a - c u} - \frac{d}{b - d u}$, a fraction with zero numerator and
zero denominator being read as $0$. For an index $\mathbf{k} = (k_1, \dots, k_r)$ of positive
integers put $\mathbf{k}{\uparrow} = (k_1, \dots, k_r + 1)$ and
$\mathbf{k}{\rightarrow} = (k_1, \dots, k_r, 1)$. The generalized multiple polylogarithm
$\mathrm{Li}_{\mathbf{k}} = \mathrm{Li}_{\mathbf{k}}(g; (\beta, \gamma); z) \in \mathbb{R}[[z]]$
is defined recursively by
$\mathrm{Li}_{(1)} = \int_0^z \left(\frac{c_0}{1 - c_0 u} + \frac{d_0}{1 + d_0 u}\right) du$,
$\mathrm{Li}_{\mathbf{k}{\uparrow}} =
\int_0^z \sum_{i=1}^{s} \beta_i G_{g_i}(u) \, \mathrm{Li}_{\mathbf{k}}(u)\,du$ and
$\mathrm{Li}_{\mathbf{k}{\rightarrow}} =
\int_0^z \sum_{i=1}^{s} \gamma_i G_{g_i}(u) \, \mathrm{Li}_{\mathbf{k}}(u)\,du$, where
integrals of power series are taken term by term. A list of natural numbers that is empty or has
a zero entry gives $0$.

## Sources

- Ken Kamano, *A Generalization of the Landen Connection Formula and Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2, display (6).
