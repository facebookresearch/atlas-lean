# Bistable wavefronts of the Gurtin–MacCamy model

**Model.** The density $u(t,a,x)$ of individuals of age $a>0$ at position $x \in \mathbb R$ obeys the diffusive Gurtin–MacCamy system
$$(\partial_t + \partial_a - \partial_{xx})\,u = -\mu(a)\,u, \qquad u(t,0,x) = f\Big(\int_0^\infty \beta(a)\,u(t,a,x)\,da\Big),$$
with measurable mortality $0 < \underline\mu \le \mu(a) \le \mu^*$ and fertility $0 \le \beta(a) < \beta^*$, normalized by $\int_0^\infty \beta(a)\Pi(a)\,da = 1$ where $\Pi(a) = e^{-\int_0^a\mu}$ is survival to age $a$. The birth function $f:[0,1]\to\mathbb R$ is $C^1$, strictly increasing and *bistable*: $f(x) = x$ exactly at $0 < \theta < 1$ (and at $0$ and $1$), with $0 < f'(0), f'(1) < 1 < f'(\theta)$. The stable stationary states are $u \equiv 0$ and $u = \Pi(a)$.

**Reduction.** A travelling wave $u = U(a,x-ct)$ is determined by the total birth profile $\phi(x) = \int_0^\infty\beta(a)U(a,x)\,da$, which solves
$$\phi(x) = \int_{\mathbb R} G_c(x-y)\,f(\phi(y))\,dy, \qquad \phi(-\infty) = 1,\ \phi(+\infty) = 0, \qquad G_c(z) = \int_0^\infty \beta(a)\Pi(a)\,K(a,z+ca)\,da,$$
with $K$ the heat kernel; then $U(a,x) = \Pi(a)\int K(a,x-y+ca)\,f(\phi(y))\,dy$. $G_c$ is a positive, bounded probability density.

**Theorem (existence and monotonicity).** There is a pair $(c,U)$ with $U \in C(\mathbb R, L^1(0,\infty))$ such that $u(t,a,x) = U(a,x-ct)$ is a bistable wavefront connecting $\Pi$ (at $-\infty$) to $0$ (at $+\infty$). Every travelling wave connecting the two stable equilibria is strictly decreasing in the space variable.

**Theorem (speed sign and tails).** (i) If $\int_0^1 (f(x) - x)\,dx > 0$, then the speed of every bistable wavefront is positive (the populated state invades). (ii) Under an additional kernel assumption, any wavefront satisfies
$$U(a,x) \sim C_0 f'(0)\,\Pi(a)\,e^{a(\lambda_0^2 - \lambda_0 c)}e^{-\lambda_0 x} \ (x\to+\infty), \qquad \Pi(a) - U(a,x) \sim C_1 f'(1)\,\Pi(a)\,e^{a(\lambda_1^2 + \lambda_1 c)}e^{\lambda_1 x} \ (x\to-\infty),$$
where $\lambda_0, \lambda_1 > 0$ are the unique positive roots of $1 = f'(0)\int e^{\lambda x}G_c(x)\,dx$ and $1 = f'(1)\int e^{-\lambda x}G_c(x)\,dx$.

## Expansion

For each candidate speed $c$, the integral equation defines a monotone, translation-invariant, compact-open continuous operator $Q_c$ on monotone profiles, generating a discrete-time recursion $u_{n+1} = Q_c[u_n]$ with bistable structure; the theory of monotone evolution systems (Fang–Zhao type) yields a unique (up to translation) monotone wave of the recursion, $Q_c[\phi_c]\,(x) = \phi_c(x + v_c)$. Continuity and monotonicity of $c \mapsto v_c$ and estimates on its sign give a $c$ with $v_c = 0$, i.e. a genuine travelling wave. The invasion condition is the bistable "positive area" criterion, and the exact exponential tails follow from Ikehara-type Tauberian theorems applied to the Laplace transforms of the profile.

## Sources

- Quentin Griette, Franco Herrera and Hao Kang, "Bistable wavefronts in the Gurtin-MacCamy population model", arXiv:2609.15853 (2026), Theorems 1.2 and 1.3, Propositions 2.1, 2.4 and 3.1, Theorem 3.3 and Theorem 4.4, <https://doi.org/10.48550/arXiv.2609.15853>.
