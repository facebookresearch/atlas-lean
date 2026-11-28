# Extinction criterion for critical state-dependent multitype Galton–Watson processes

**State-dependent multitype Galton–Watson process.** Let $Z_n \in \mathbb N^d$ count individuals of $d$ types. Given $Z_n = z$, each type-$i$ individual independently produces an offspring vector $(X_{i,1}(z),\dots,X_{i,d}(z))$ whose law depends only on $i$ and the current state $z$. Assume the mean matrix is $M(z) = M + C(z)$ with $M$ non-negative primitive with Perron root $1$ (right and left eigenvectors $u$, $v$, $vu = u^\top u = 1$) and $C(z) \ge 0$, that $g(z) = zC(z) \to D \in \mathbb R_+^d$ as $\|z\| \to \infty$, that the offspring covariance matrices $\Gamma_i(z)$ converge to $\Gamma_i$, that $E(X_{i,j}(z)^{2+\delta}) < K$ uniformly, that $0$ is absorbing and all other states communicate. Let $V(z) = \sum_{i=1}^d z_i \Gamma_i$.

**Theorem (Adam, Theorem 3.1).**

- If $\dfrac{2Du}{u^\top V(v) u} < 1$, the process becomes extinct almost surely.
- If $\dfrac{2Du}{u^\top V(v) u} > 1$, the process survives with positive probability.

**Corollary (Adam, Corollary 3.1; two-type cell division).** In Klebaner's two-type cell division model with Bernoulli offspring indicators, base mean matrix with rows $(p, 1-p)$ and $(p', 1-p')$, density-dependent corrections of total strengths $c_1, c_2 > 0$, and probabilities $b_i$ that a type-$i$ cell has offspring of both types,

$$c_1 + c_2 < \frac{p'}{1-p+p'}\, b_1 + \frac{1-p}{1-p+p'}\, b_2 \;\Rightarrow\; \text{almost sure extinction},$$

and the reverse strict inequality gives survival with positive probability. This sharpens Klebaner's bounds ($c_1 + c_2 < \min(b_1,b_2)$ for extinction, $c_1 + c_2 > \max(b_1,b_2)$ for survival).

**Proposition (Adam, Proposition 3.1; immigration).** Let $(Z_n)$ be a critical multitype Galton–Watson process with immigration: offspring vectors are independent with laws depending only on the parent's type, $P(X_{i,j} = 0) > 0$ for all $i, j$, the mean matrix $M$ is non-negative and primitive with Perron root $1$, and at each generation an immigrant vector $A_n$ arrives, the $A_n$ being i.i.d., independent of all offspring variables, with $P(A_1 = 0) > 0$, $E(A_1) = a$ and $\operatorname{Var}(A_1u) < \infty$; assume $E(X_{i,j}^{2+\delta}) < \infty$ and $E((A_1u)^{2+\delta}) < \infty$ for some $\delta > 0$. Then $(Z_n)$ is recurrent if $2au < u^\top V(v)u$ and transient if $2au > u^\top V(v)u$, recovering Kawazu's criterion.

## Depends on

- [Unlimited growth criterion for critical stochastic difference equations](unlimited-growth-criterion-for-critical-stochastic-difference-equations.md)

## Expansion

Writing $Z_{n+1} = Z_n M + g(Z_n) + \xi_n$ with $\xi_n$ the centered offspring sum puts the process in the setting of the unlimited growth criterion with $\alpha = 0$: the drift along $u$ is $g(Z_n)u \to Du$, so $c_1 = Du$, and $E((\xi_n u)^2 \mid \mathcal F_n) = (Z_n u)\, u^\top V(v) u + (\text{transverse and lower-order terms})$, so $d_1 = u^\top V(v)u$. The condition $c_1 \gtrless d_1/2$ becomes $2Du \gtrless u^\top V(v)u$. Since $0$ is absorbing and other states communicate, "does not tend to infinity" means extinction. For the immigration process the drift is the constant $a$, giving $c_1 = au$; there escape to infinity is transience.

## Sources

- E. Adam, *Criterion of unlimited growth for critical multidimensional stochastic models*, arXiv:1502.04046 (2015). <https://doi.org/10.48550/arXiv.1502.04046>. Published version: Advances in Applied Probability 48(4) (2016), 972–988, <https://doi.org/10.1017/apr.2016.61>; locators above refer to the arXiv version.
