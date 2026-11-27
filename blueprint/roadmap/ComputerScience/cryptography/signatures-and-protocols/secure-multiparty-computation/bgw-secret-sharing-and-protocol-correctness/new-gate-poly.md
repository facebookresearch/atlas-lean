# Sharing polynomial of a new BGW gate

Let $F$ be a field and $\mathrm{Party}$ a finite type of parties, with Shamir parameters giving a threshold $t$ and an evaluation point $\alpha_i \in F$ for each party $i$, and let $\lambda : \mathrm{Party} \to F$ be arbitrary weights (the definition assumes no recombination property of $\lambda$). For a gate with operation $\mathrm{op} \in \{+, \times\}$, argument wires $w_0, w_1$, an assignment $P$ of a polynomial over $F$ to each wire computed so far, and a tape $\tau : \mathrm{Party} \to F^t$, the sharing polynomial of the new gate is defined by cases:

- **addition:** $P(w_0) + P(w_1)$ (the weights and the tape are unused);
- **multiplication:**

$$
\sum_{i \in \mathrm{Party}} \lambda_i \cdot S_i, \qquad S_i = \text{the Shamir sharing polynomial with secret } \bigl(P(w_0)\,P(w_1)\bigr)(\alpha_i) \text{ and random coefficients } \tau_i .
$$

Each $S_i$ has constant term $(P(w_0)P(w_1))(\alpha_i)$, the product of party $i$'s two argument shares when the $P(w_j)$ are the sharing polynomials, and degree at most $t$.
