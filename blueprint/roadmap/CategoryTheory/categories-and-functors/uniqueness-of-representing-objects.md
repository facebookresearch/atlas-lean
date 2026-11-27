# Representing objects are unique up to isomorphism

Let $\mathcal{C}$ be a category and $F \colon \mathcal{C}^{\mathrm{op}} \to \mathbf{Set}$ a presheaf
of sets, and suppose that objects $Y$ and $Y'$ of $\mathcal{C}$ both represent $F$: there are
bijections $e_X \colon \operatorname{Hom}(X, Y) \to F(X)$ and $e'_X \colon \operatorname{Hom}(X, Y')
\to F(X)$, natural in $X$. Then the morphism $Y \to Y'$ that corresponds to $\mathrm{id}_Y$ under
the bijection $(e'_Y)^{-1} \circ e_Y \colon \operatorname{Hom}(Y, Y) \to \operatorname{Hom}(Y, Y')$
is an isomorphism.

## Sources

- The Stacks Project, Lemma 4.3.5 (Yoneda lemma), <https://stacks.math.columbia.edu/tag/001P>, and
  Definition 4.3.6, <https://stacks.math.columbia.edu/tag/001Q>.
