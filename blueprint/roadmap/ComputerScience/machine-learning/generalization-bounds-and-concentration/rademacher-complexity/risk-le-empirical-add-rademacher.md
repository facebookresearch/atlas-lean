# The Rademacher risk bound

Let $P$ be a probability measure on $X \times Y$, let $\mathcal{F}$ be a finite class of functions $X \to \mathcal{A}$, and let $L \le \varphi$ be a loss and a dominating cost with $0 \le L$ and $\varphi \le 1$, measurable along every $f \in \mathcal{F}$. For $n \ge 1$ and $0 < \delta < 1$, with probability at least $1 - \delta$ over an i.i.d. sample $S = ((X_i, Y_i))_{i \le n} \sim P^n$, every $f \in \mathcal{F}$ satisfies

$$\mathbb{E}_P\, L(Y, f(X)) \le \frac{1}{n} \sum_{i=1}^n \varphi(Y_i, f(X_i)) + 2\, \mathbb{E}_{S'}\, R\big(\varphi \circ \mathcal{F}|_{S'}\big) + \sqrt{\frac{8 \log(2/\delta)}{n}},$$

where $\varphi \circ \mathcal{F}|_{S'}$ is the set of cost vectors $(\varphi(Y'_i, f(X'_i)))_i$.

This is Bartlett and Mendelson's Theorem 8 in the convention of this topic: their proof (McDiarmid's inequality, then symmetrization with a ghost sample) ends with $2\, \mathbb{E} \sup_h \frac{1}{n} \sum_i \sigma_i h(X_i, Y_i)$, which is the middle term above and is at most their $R_n(\tilde\varphi \circ F)$; the recentring $\tilde\varphi$ is unnecessary here by translation invariance. The finite class is a restriction that makes every quantity measurable; the source states the result for general classes. For $\varphi = L$, Shalev-Shwartz and Ben-David's Theorem 26.5 (part 1) gives the same bound with the sharper deviation term $\sqrt{2 \log(2/\delta)/n}$.

## Informally uses

- [Concentration of the uniform deviation](../bounded-differences-uniform-deviation.md): mathematical prerequisite, the bounded-differences step of the proof.
- [Translation invariance](rademacher-complexity-add-singleton.md): why the costs need no recentring.

## Background

- [The contraction lemma](rademacher-complexity-coord-map-le.md): applied with a Lipschitz margin cost, it turns this into Bartlett and Mendelson's margin bound (their Theorem 7). That margin bound is a consequence of this theorem; the lemma is not a step of its proof.
- [The margin costs of voting classifiers are no more complex than the base classifiers](rademacher-complexity-margin-costs-conve.md): the complexity term of that margin bound when the class is a convex hull, as for boosting.

## Sources

- P. L. Bartlett and S. Mendelson, *Rademacher and Gaussian complexities: risk bounds and structural results*, Journal of Machine Learning Research 3 (2002) 463–482, <https://jmlr.csail.mit.edu/papers/volume3/bartlett02a/bartlett02a.pdf>, Theorem 8 and its proof, pages 467–468.
- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press (2014), Theorem 26.5, part 1, and Lemma 26.2 (symmetrization).
