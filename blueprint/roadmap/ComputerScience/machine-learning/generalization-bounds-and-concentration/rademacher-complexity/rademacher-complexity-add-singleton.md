# Translation invariance

For nonempty bounded $A \subseteq \mathbb{R}^n$ and every $v \in \mathbb{R}^n$, $R(A + \{v\}) = R(A)$. In Bartlett and Mendelson's absolute-value convention the corresponding statement is the inequality $R_n(F + h) \le R_n(F) + \lVert h \rVert_\infty / \sqrt{n}$. Translation invariance is what lets a risk bound use the costs $\varphi(y, f(x))$ directly instead of the recentred costs $\varphi(y, f(x)) - \varphi(y, 0)$.

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press (2014), Lemma 26.6 (the inequality $R(cA + a_0) \le \lvert c \rvert R(A)$; with $c = 1$ it gives $\le$, and equality follows from it applied with $a_0$ and $-a_0$).
- P. L. Bartlett and S. Mendelson, *Rademacher and Gaussian complexities: risk bounds and structural results*, Journal of Machine Learning Research 3 (2002) 463–482, <https://jmlr.csail.mit.edu/papers/volume3/bartlett02a/bartlett02a.pdf>, Theorem 12, part 5 (the inequality in their convention).
