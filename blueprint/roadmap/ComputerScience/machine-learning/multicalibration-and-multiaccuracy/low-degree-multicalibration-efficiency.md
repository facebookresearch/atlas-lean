# Low-degree multicalibration captures the guarantees of multicalibration at lower cost

Low-degree multicalibration of a small fixed degree already gives guarantees of multicalibration that multiaccuracy does not. Write $\mathbb{E}_c[g] = \mathbb{E}[c(x)g(x)]/\mathbb{E}[c(x)]$ for the expectation reweighted by $c \in \mathcal{C}$ with $\mathbb{E}[c] > 0$. If $p$ is degree-$k$ $0$-multicalibrated with respect to $\mathcal{C}$, $k \ge 2$, then for every such $c$ and every $d \le k$

$$
\mathbb{E}_c[(p^*)^d] \ \ge\ \mathbb{E}_c[p^d] \ =\ \mathbb{E}_c[p^{d-1}p^*] \ \ge\ \mathbb{E}_c[p^{d-1}]\;\mathbb{E}_c[p^*] ;
$$

so within each $c$ the predictions are not overconfident (for $k = 2$, their variance is at most that of $p^*$ and their mean equals that of $p^*$) and are positively correlated with the outcome. This yields bounds on the generalized true and false positive rates of $p$ within each $c$ in terms of those of $p^*$. When $\mathcal{C}$ contains the constant function $1$, degree-$2$ $0$-multicalibration also gives the Pythagorean identity $\mathbb{E}[(c - p^*)^2] = \mathbb{E}[(p - p^*)^2] + \mathbb{E}[(c - p)^2]$ for every $c \in \mathcal{C}$, hence $\mathbb{E}[(p - p^*)^2] \le \min_{c \in \mathcal{C}} \mathbb{E}[(c - p^*)^2]$, a squared-loss form of omniprediction; whether the omniprediction guarantees of full multicalibration for general losses follow from low degree is left open. Algorithmically, a weak agnostic learner for $\mathcal{C}$ yields $(\mathcal{C}, W, \alpha)$-multicalibration for any finite weight class $W$ with a number of learner calls polynomial in $|W|$ and $1/\alpha$. With $\ell$ classes and a sample-optimal weak learner, degree-$(k+1)$ $\alpha$-multicalibration needs $\tilde O\big(\ell\,(\mathrm{VC}(\mathcal{C}) + k)/\alpha^4\big)$ samples, polynomial in $\ell$, whereas obtaining it through smooth or full multicalibration costs a factor exponential in $\ell$.

## Proof sketch

The middle equality is the degree-$k$ condition with weight $z^{d-1}$. The left inequality follows from Hölder's inequality, $\mathbb{E}_c[p^{d-1}p^*] \le \mathbb{E}_c[p^d]^{(d-1)/d}\,\mathbb{E}_c[(p^*)^d]^{1/d}$, combined with the equality; the right one says that the covariance of $p^{d-1}$ and $y$ under the reweighting is nonnegative. With $\alpha > 0$ the same bounds hold up to additive terms of order $d\alpha/\mathbb{E}[c]$. For the Pythagorean identity, multiaccuracy gives $\mathbb{E}[c\,p^*] = \mathbb{E}[c\,p]$ and the degree-$2$ condition with $c = 1$ and weight $z$ gives $\mathbb{E}[p\,p^*] = \mathbb{E}[p^2]$; expanding the squares gives the identity. The algorithm is boosting with the weak learner as auditor on the residuals weighted by $w(p(x))$, as in the multicalibration algorithm, with a potential argument bounding the number of rounds; the sample bounds compare the size of the needed weight bases.

## Depends on

- [Low-degree multicalibration](low-degree-multicalibration.md)
- [Multiaccurate predictors](multiaccurate-predictor.md)
- [Multicalibrated predictors](multicalibrated-predictor.md)

## Proof depends on

- [Multicalibration by iterated level-set corrections terminates quickly](multicalibration-iterative-algorithm.md)

## Sources

- P. Gopalan, M. P. Kim, M. Singhal, S. Zhao, "Low-Degree Multicalibration", COLT (2022), arXiv:2203.01255, Theorems 2, 3, 4.2 and 5.5, Section 2.
