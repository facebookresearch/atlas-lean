# The index of a principal ideal of an order

Let $K$ be a number field, $O$ an order in
$K$ (`NumberField.IsOrder`), and for $\beta \in K$ let $N_{K/\mathbb{Q}}(\beta)$
(`Algebra.norm ℚ`) be the determinant of the $\mathbb{Q}$-linear map $x \mapsto \beta x$ of
$K$. Then for every nonzero $\beta \in O$,

$$[O : \beta O] = \#(O/\beta O) = \bigl|N_{K/\mathbb{Q}}(\beta)\bigr|,$$

as an identity of rational numbers.

This is A. V. Sutherland, MIT 18.783 Lecture 17 (Fall 2023), Lemma 17.5 (p. 3), with the norm of
Definition 17.3 (p. 2), and K. Conrad, *The conductor ideal of an order*, footnote 4 (p. 14);
F. Keune, *Number Fields*, 2023, Proposition 3.20 (p. 58), proves it for $O = \mathcal{O}_K$.
