# On-average replace-one stability

Let $m \ge 1$, let $A$ be a possibly randomized learner mapping samples of size $m$ to hypotheses, and let $\ell$ be a loss
with $\ell(A(S), z)$ integrable. Draw $S = (z_1, \dots, z_m) \sim D^m$, $z' \sim D$ and $i$ uniform on $\{1, \dots, m\}$,
independently of each other and of $A$'s randomness, and let $S^{(i)}$ be $S$ with $z_i$ replaced by $z'$. The learner is
on-average-replace-one-stable with rate $\varepsilon(m)$ if
$\mathbb{E}[\ell(A(S^{(i)}), z_i) - \ell(A(S), z_i)] \le \varepsilon(m)$ for every distribution $D$, the expectation being
over all of these and $A$'s randomness.

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Definition 13.3 (on-average-replace-one-stable). <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
