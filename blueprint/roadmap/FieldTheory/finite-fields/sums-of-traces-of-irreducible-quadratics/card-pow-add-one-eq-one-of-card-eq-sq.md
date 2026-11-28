# $\mathbb{F}_{q^2}$ has exactly $q + 1$ elements with $\beta^{q+1} = 1$

Let $K$ be a finite
field with $q^2$ elements. Then exactly $q + 1$ elements $\beta \in K$ satisfy
$\beta^{q + 1} = 1$.

For the quadratic extension $K \supseteq \mathbb{F}_q$, $\beta^{q+1}$ is the norm of $\beta$
(`FiniteField.card_norm_eq_one_of_card_eq_sq` states the count with `Algebra.norm`). The source
takes $q$ to be a prime power; that follows from $\# K = q^2$, so it is not a hypothesis here.

## Sources

- B. Poonen, "Characterizing integers among rational numbers with a universal-existential formula", Amer. J. Math. 131 (2009), 675–682, proof of Lemma 2.3, read in the author's version with the corrections of April 15, 2019, p. 3: "Since $\mathbb{F}_{q^2}$ contains $q + 1$ norm-1 elements, $U_q \neq \emptyset$", with $N$ the norm for $\mathbb{F}_{q^2}/\mathbb{F}_q$.
