# Massart's finite-class lemma

Let $A \subseteq \mathbb{R}^n$ be finite and nonempty, and let $r \ge 0$ with $\lVert a \rVert_2 \le r$ for every $a \in A$. Then

$$R(A) \le \frac{r \sqrt{2 \log \lvert A \rvert}}{n}.$$

The proof bounds $\exp(\lambda \cdot \text{average supremum})$ by Jensen's inequality, the maximum by the sum over $A$, and each exponential moment by $\prod_i \cosh(\lambda a_i) \le \exp(\lambda^2 \lVert a \rVert_2^2 / 2)$, then optimizes over $\lambda > 0$.

## Informally uses

- [Exponential moment of a Rademacher sum](average-exp-sign-corr-le.md): builds on.

## Sources

- P. Massart, *Some applications of concentration inequalities to statistics*, Annales de la Faculté des Sciences de Toulouse, Mathématiques 9 (2000) 245–303, Lemma 5.2.
- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press (2014), Lemma 26.8 (stated there with $\max_a \lVert a - \bar a \rVert$, the vectors centred at their mean $\bar a$; the uncentred form here is Massart's, and is what their proof gives without the centring step).
