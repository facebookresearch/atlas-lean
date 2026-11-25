# Recurrence for appending the entry 1

Let $g = (g_0, g_1, \dots, g_s)$ be Landen data and
let $\beta, \gamma \in \mathbb{R}^s$. For every nonempty list $\mathbf{k} = (k_1, \dots, k_r)$ of
natural numbers,
$\mathrm{Li}_{(k_1, \dots, k_r, 1)}(g; (\beta, \gamma); z) =
\int_0^z \sum_{i=1}^{s} \gamma_i G_{g_i}(u) \, \mathrm{Li}_{\mathbf{k}}(g; (\beta, \gamma); u)\,du$,
where $u \sum_{i} \gamma_i G_{g_i}(u)$ is the weighted form series of $g$ with weights $\gamma$
and the integral of a power series is taken term by term.

## Sources

- Ken Kamano, *A Generalization of the Landen Connection Formula and Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2.
