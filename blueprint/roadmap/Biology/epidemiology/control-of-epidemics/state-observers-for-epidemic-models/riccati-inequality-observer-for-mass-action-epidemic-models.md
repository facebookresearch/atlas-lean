# Riccati-inequality observer for mass-action epidemic models

Many compartmental and networked epidemic models (SIR, SEIR, SIDARTHE and their metapopulation versions) have the form

$$ \dot x = A x + G f(Hx), \qquad y = C x, $$

with state $x(t) \in \mathcal X \subset \mathbb R^{n_x}$ on a bounded domain, measured output $y \in \mathbb R^{n_y}$, matrices $A \in \mathbb R^{n_x\times n_x}$, $G \in \mathbb R^{n_x\times n_f}$, $H \in \mathbb R^{k\times n_x}$, $C \in \mathbb R^{n_y\times n_x}$, and a polynomial (mass-action) nonlinearity $f$, which is Lipschitz on $\mathcal X$: $\|f(Hx) - f(H\hat x)\| \le \ell \|H(x - \hat x)\|$. Assume $(A, C)$ is detectable.

**Observer.** With gains $J, L \in \mathbb R^{n_x\times n_y}$ and $K \in \mathbb R^{k\times n_y}$, set $M = A - LCA - JC$, $N = I - LC$ and

$$ \dot z = M z + (ML + J) y + N G f(v), \qquad v = H\hat x + K(y - C\hat x), \qquad \hat x = z + L y . $$

The estimation error $e = x - \hat x$ obeys $\dot e = M e + NG\,[f(Hx) - f(v)]$, and $\|f(Hx) - f(v)\| \le \ell \|(H - KC) e\|$.

**Theorem (Lipschitz criterion).** If there are $P \succ 0$ and gains $J, L, K$ with

$$ M^{\top} P + P M + P N G G^{\top} N^{\top} P + \ell^2 (H - KC)^{\top}(H - KC) \prec 0, $$

then $e(t) \to 0$ as $t \to \infty$. This algebraic Riccati inequality holds if and only if there are $P, Q \succ 0$, $K$ and $R, S \in \mathbb R^{n_x\times n_y}$ such that the linear matrix inequalities

$$ \begin{pmatrix} \operatorname{sym}(PA - RCA - SC) + Q & (P - RC) G \\ G^{\top}(P - RC)^{\top} & -I \end{pmatrix} \prec 0, \qquad \begin{pmatrix} -Q & (H - KC)^{\top} \\ H - KC & -\ell^{-2} I \end{pmatrix} \preceq 0 $$

are feasible, with $\operatorname{sym}(X) = X + X^{\top}$; the gains are then $J = P^{-1} S$ and $L = P^{-1} R$.

**Theorem (generalized Lipschitz criterion).** If instead $\|f(Hx) - f(H\hat x)\|_V \le \|H(x - \hat x)\|_W$ on $\mathcal X$ for some $V, W \succ 0$ (where $\|a\|_V^2 = a^{\top} V a$), the same conclusion holds under

$$ M^{\top} P + P M + P N G V^{-1} G^{\top} N^{\top} P + (H - KC)^{\top} W (H - KC) \prec 0, $$

equivalently the LMIs above with $-I$ replaced by $-V$ and $-\ell^{-2} I$ by $-W^{-1}$.

## Expansion

The quadratic incidence terms make the global Lipschitz constant of an epidemic model on its compact simplex large, so the classical Luenberger-type Lipschitz criteria are infeasible. The observer gains two extra levers. The feedforward injection $Ly$ multiplies the nonlinearity in the error equation by $N = I - LC$, which can shrink or annihilate the directions in which $G$ acts; the innovation $K(y - C\hat x)$ inside $f$ replaces $H$ by $H - KC$ in the Lipschitz bound. With $V(e) = e^{\top} P e$ and Young's inequality $2 e^{\top} P N G \tilde f \le e^{\top} P N G G^{\top} N^{\top} P e + \|\tilde f\|^2$, the Riccati inequality makes $\dot V$ negative definite. The generalized version uses the lemma $2\xi^{\top}\Gamma^{\top}\tilde f \le \|\Gamma\xi\|^2_{V^{-1}} + \|\xi\|^2_W$ for $\xi = H(x - \hat x)$. A Schur complement with the substitutions $R = PL$, $S = PJ$ linearizes the inequality. The paper applies the design to the SIDARTHE-V COVID-19 model. These are Theorem 1, Corollary 1.1, Lemma 2, Theorem 3 and Corollary 3.1 of the source.

## Sources

- M. U. B. Niazi and K. H. Johansson, *Observer Design for the State Estimation of Epidemic Processes*, arXiv:2207.11977 (2022), Section "Proposed Observer Design", Theorems 1 and 3, Corollaries 1.1 and 3.1, Lemma 2. <https://doi.org/10.48550/arXiv.2207.11977> Published version: 2022 IEEE 61st Conference on Decision and Control (CDC) (2022) 4325–4332, <https://doi.org/10.1109/cdc51059.2022.9993275>.
