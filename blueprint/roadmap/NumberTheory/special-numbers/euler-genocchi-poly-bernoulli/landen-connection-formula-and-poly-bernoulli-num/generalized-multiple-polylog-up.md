# Recurrence for raising the last entry

Let $g = (g_0, g_1, \dots, g_s)$ be Landen data and
let $\beta, \gamma \in \mathbb{R}^s$. For every list $(k_1, \dots, k_{r-1})$ of natural numbers
(possibly empty) and every natural number $m$, writing $\mathbf{k} = (k_1, \dots, k_{r-1}, m + 1)$,
$\mathrm{Li}_{(k_1, \dots, k_{r-1}, m + 2)}(g; (\beta, \gamma); z) =
\int_0^z \sum_{i=1}^{s} \beta_i G_{g_i}(u) \, \mathrm{Li}_{\mathbf{k}}(g; (\beta, \gamma); u)\,du$,
where $u \sum_{i} \beta_i G_{g_i}(u)$ is the weighted form series of $g$ with weights $\beta$
and the integral of a power series is taken term by term.

## Sources

- Ken Kamano, *A Generalization of the Landen Connection Formula and Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2.
