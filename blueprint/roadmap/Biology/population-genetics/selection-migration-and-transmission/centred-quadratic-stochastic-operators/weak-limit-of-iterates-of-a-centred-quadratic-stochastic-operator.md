# Weak limit of iterates of a centred quadratic stochastic operator

A **quadratic stochastic operator** on finite signed measures is a symmetric bilinear map $\mathbf{Q}$ with $\|\mathbf{Q}(F_1,F_2)\|_{TV} = \|F_1\|_{TV}\|F_2\|_{TV}$ that maps pairs of non-negative measures to non-negative measures; its iterates on probability measures are $\mathbb{Q}^{n+1}(F) = \mathbf{Q}(\mathbb{Q}^n(F), \mathbb{Q}^n(F))$. For a probability measure $G$ on $\mathbb{R}^d$ the **centred** quadratic stochastic operator is

$$\mathbf{Q}_G(F_1,F_2) = \dot F_1 * \dot F_2 * G, \qquad \dot F(A) := F(2A),$$

i.e. the offspring trait is $\tfrac12(X + X') + Y$ with independent parental traits $X \sim F_1$, $X' \sim F_2$ and perturbation $Y \sim G$. Write $H^{(n)} = \mathbb{Q}_G^n(F)$.

**Theorem.**

*(1)* (Finite variance) Let $F$ have finite mean $m \in \mathbb{R}^d$ and $G$ finite first and second moments with mean $0$. Then $H^{(n)}$ converges weakly to a probability measure $H^{(\infty)}$ with characteristic function

$$\varphi_{H^{(\infty)}}(s) = e^{i m\cdot s}\lim_{n\to\infty}\prod_{j=0}^{n-1}\Big(\varphi_G\big(s/2^j\big)\Big)^{2^j}, \qquad s \in \mathbb{R}^d.$$

*(2)* (Fixed-point equation, $d = 1$) If $\mathbf{Q}_G$ is weakly asymptotically stable at $F$ with limit $H^{(\infty)}$, then $\varphi_{H^{(\infty)}}(s) = \big(\varphi_{H^{(\infty)}}(s/2)\big)^2\varphi_G(s)$ for all $s$. Conversely, $H$ is the weak limit of $\mathbb{Q}^n_G(F)$ for some $F, G$ if and only if $\varphi_H(s) = (\varphi_H(s/2))^2\varphi(s)$ for some characteristic function $\varphi$.

*(3)* (Heavy tails, $d = 1$) If $G$ is symmetric with $G(-\infty,-x] = G[x,\infty) \le C x^{-(1+\epsilon)}$ for all $x > 0$ and some $\epsilon \in (0,1)$, then $|1 - \varphi_G(s)| < C'|s|^{1+\epsilon}$, which suffices for the infinite product to converge; perturbations with Cauchy-type tails (exponent $\epsilon = 0$) correspond to the stable-index-one case, where $(\varphi_G(s/n))^n \to e^{-C\pi|s|}$.

## Proof depends on

- [Lévy's continuity theorem](../../../../Probability/characteristic-functions/levy-continuity-theorem/levy-continuity-of-char-fun.md)

## Expansion

The characteristic function of $\mathbf{Q}_G(F,F)$ is $\varphi_F(s/2)^2\varphi_G(s)$, and iterating gives $\varphi_{H^{(n)}}(s) = \varphi_F(s/2^n)^{2^n}\prod_{j=0}^{n-1}\varphi_G(s/2^j)^{2^j}$. Thus $H^{(n)}$ is the law of $X^{(n)} + Y^{(n)}$ with $X^{(n)} = 2^{-n}(X_1 + \dots + X_{2^n})$, a sample mean of $2^n$ founder traits, and $Y^{(n)} = \sum_{j=0}^{n-1} 2^{-j}(Y_{j,1} + \dots + Y_{j,2^j})$, a weighted sum of independent perturbations. By the law of large numbers $X^{(n)} \to m$, while $\operatorname{Var}(Y^{(n)}) = \sum_j 2^{-j}\operatorname{Var}(Y) < \infty$, giving convergence of $Y^{(n)}$; the power-tail condition replaces the variance with a summable bound $\sum_j 2^j |s/2^j|^{1+\epsilon}$. The same representation yields an exact simulation algorithm for $H^{(n)}$.

## Sources

- Krzysztof Bartoszek, Joachim Domsta and Małgorzata Pułka, *Weak stability of centred quadratic stochastic operators*, Bull. Malays. Math. Sci. Soc. 42(4) (2019), 1813–1830. <https://doi.org/10.1007/s40840-017-0575-8> Definitions 2.1, 2.3, 3.1, Theorem 4.1, Theorem 4.3, Theorem 4.5, Proposition 5.1, Corollary 5.3, Section 6. Locators use the numbering of the preprint, titled *Centred quadratic stochastic operators*, arXiv:1511.07506.
