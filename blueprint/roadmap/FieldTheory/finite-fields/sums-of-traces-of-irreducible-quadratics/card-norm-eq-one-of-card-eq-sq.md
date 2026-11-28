# The norm-one elements of $\mathbb{F}_{q^2}$ over $\mathbb{F}_q$

Let $L / K$ be an extension
of finite fields with $\# K = q$ and $\# L = q^2$. Then exactly $q + 1$ elements $\beta \in L$ have
norm $N_{L/K}(\beta) = 1$.

The norm is $\beta^{q+1}$ (`FiniteField.algebraMap_norm_eq_pow`), so this is
`FiniteField.card_pow_add_one_eq_one_of_card_eq_sq`.

## Sources

- B. Poonen, "Characterizing integers among rational numbers with a universal-existential formula", Amer. J. Math. 131 (2009), 675–682, proof of Lemma 2.3, read in the author's version with the corrections of April 15, 2019, p. 3: "Since $\mathbb{F}_{q^2}$ contains $q + 1$ norm-1 elements, $U_q \neq \emptyset$".
