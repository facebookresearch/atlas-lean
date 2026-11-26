# Mixed bias property of a functional and the form of its influence function

Let $O$ be a random vector with law $P_\eta$ in a nonparametric model $\mathcal M = \{P_\eta\}$, containing covariates $Z$, and let $\chi(\eta)$ be a regular scalar parameter with (unique) influence function $\chi^1_\eta(O)$, $\mathbb E_\eta\chi^1_\eta = 0$. The *one-step estimator* is $\hat\chi = \chi(\hat\eta) + \mathbb P_n\chi^1_{\hat\eta}$; with cross-fitting its $\sqrt n$-asymptotic normality hinges on the second-order remainder

$$\chi(\hat\eta) - \chi(\eta) + \mathbb E_\eta\chi^1_{\hat\eta} = o_p(n^{-1/2}). \tag{1}$$

**Definition (mixed bias property).** $\chi$ has the mixed bias property if for each $\eta$ there are functions $a(Z) = a(Z;\eta)$, $b(Z) = b(Z;\eta)$ and a known function $s_{ab}$ (not depending on $\eta$), $S_{ab} = s_{ab}(O)$, such that for every $\eta'$

$$\chi(\eta') - \chi(\eta) + \mathbb E_\eta\chi^1_{\eta'} = \mathbb E_\eta\big[S_{ab}\{a'(Z) - a(Z)\}\{b'(Z) - b(Z)\}\big], \tag{2}$$

with $a' = a(\cdot;\eta')$, $b' = b(\cdot;\eta')$.

Consequently, if $\|\hat a - a\|_{L_2} = O_p(\gamma_{a,n})$ and $\|\hat b - b\|_{L_2} = O_p(\gamma_{b,n})$ (and $S_{ab}$ is bounded), the remainder (1) is $O_p(\gamma_{a,n}\gamma_{b,n})$, and the cross-fitted estimator is $\sqrt n$-asymptotically normal whenever $\gamma_{a,n},\gamma_{b,n} \to 0$ and $\gamma_{a,n}\gamma_{b,n} = o(n^{-1/2})$ (*rate double robustness*).

**Proposition.** Under the mixed bias property (and regularity), $\chi(\eta) + \chi^1_\eta$ depends on $\eta$ only through $(a,b)$.

**Theorem (characterization).** If $\chi$ has the mixed bias property and regularity holds, there are a statistic $S_0$ and maps $h \mapsto m_1(O,h)$, $h \mapsto m_2(O,h)$ not depending on $\eta$, with $h \mapsto \mathbb E_\eta m_i(O,h)$ linear, such that

$$\chi(\eta) = \mathbb E_\eta\{m_1(O,a)\} + \mathbb E_\eta(S_0) = \mathbb E_\eta\{m_2(O,b)\} + \mathbb E_\eta(S_0), \tag{3}$$

$$\chi^1_\eta = S_{ab}\,a(Z)\,b(Z) + m_1(O,a) + m_2(O,b) + S_0 - \chi(\eta), \tag{4}$$

and $\mathbb E_\eta\{S_{ab}hb + m_1(O,h)\} = 0$, $\mathbb E_\eta\{S_{ab}ha + m_2(O,h)\} = 0$ for all admissible $h$. Conversely, an influence function of form (4) with continuous linear $h \mapsto \mathbb E_\eta m_i(O,h)$ (Riesz representers $R_1, R_2$) implies (2), and if $\mathbb E_\eta(S_{ab}\mid Z) \ne 0$ a.s. then $a = -R_2/\mathbb E_\eta(S_{ab}\mid Z)$ and $b = -R_1/\mathbb E_\eta(S_{ab}\mid Z)$.

Example: for $O = (DY, D, Z)$ with $Y$ missing at random given $Z$ and observed iff $D = 1$, the mean of $Y$ is $\chi(\eta) = \mathbb E_\eta\{a(Z)\}$ with $a(Z) = \mathbb E_\eta(DY\mid Z)/\mathbb E_\eta(D\mid Z)$, and it has the mixed bias property with $b(Z) = 1/\mathbb E_\eta(D\mid Z)$ and $S_{ab} = -D$. In general the class contains both the Robins et al. (2008) class and the Chernozhukov et al. doubly robust class of linear functionals, strictly.

## Depends on

- [Riesz representer and the doubly robust moment of a linear functional](riesz-representer-and-doubly-robust-moment.md)

## Expansion

Equation (2) says the first-order Taylor remainder of $\chi$ is exactly a bilinear form in the errors of $a$ and $b$, so by Cauchy–Schwarz it is bounded by the product of their $L_2$ errors. Taking $\eta' $ that changes only $a$ (or only $b$) makes the right side of (2) vanish, which yields the moment equations for $a$ and $b$ and, by linearity, the representation (3)–(4).

## Sources

- Andrea G. Rotnitzky, Ezequiel Smucler and James M. Robins, "Characterization of parameters with a mixed bias property", Biometrika (2020), <https://doi.org/10.1093/biomet/asaa054>. arXiv:1904.03725. Eqs. (1)–(4), Definition 1, Proposition 1, Theorems 1 and 2, Example 1.
