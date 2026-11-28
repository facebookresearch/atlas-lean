# Weight-percent and atomic-percent conversion round trips

Let $\iota$ be a finite nonempty index set and $M : \iota \to \mathbb{R}$ molar masses with $M_i > 0$ for all $i$. Write $\mathrm{mf}(M, n)_i = n_i M_i / \sum_j n_j M_j$ for the mass fraction and $\mathrm{xf}(M, w)_i = (w_i / M_i) / \sum_j (w_j / M_j)$ for the mole fraction of a mass-fraction vector $w$. Then:

1. for every $w : \iota \to \mathbb{R}$ with $w_i > 0$ for all $i$ and $\sum_i w_i = 100$, normalizing to the simplex, converting to mole fractions and taking weight percent recovers $w$: $\mathrm{wt\%}(M, \mathrm{xf}(M, w / 100)) = w$;
2. for every $x : \iota \to \mathbb{R}$ with $x_i > 0$ for all $i$ and $\sum_i x_i = 1$, $\mathrm{at\%}(\mathrm{xf}(M, \mathrm{mf}(M, x))) = \mathrm{at\%}(x)$.
