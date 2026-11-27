# Large-population asymptotics of Moran game fixation probabilities

**Setting.** The two-strategy Moran game of [Graph shapes of the fixation probability in each evolutionary scenario of the two-strategy Moran game](graph-shapes-of-the-fixation-probability-in-each-evolutionary-scenario.md), with pay-offs $a, b, c, d > 0$ and fixed intensity of selection $w$. As $N \to \infty$ with $i = [Nx]$, the relative fitness $r_i$ converges to

$$
R(x) = \frac{1 - w + w[ax + b(1-x)]}{1 - w + w[cx + d(1-x)]},
$$

and the *fitness potential* is $L(x) = -\int_0^x \log R(t)\, dt$. For large $N$ the invasion scenario is read off the signs of $R(0) - 1$ and $R(1) - 1$. Write $\Pi_N(x) = \pi_{[Nx]}$ for the fixation probability of $A$ from initial fraction $x$, and take $x \in \mathbb{Q}_{N_0} = \{j/N_0\}$ with $N$ a multiple of $N_0$.

**Theorem.**

1. *(Dominance.)* If the invasion scenario is $B \overset{\rightarrow\rightarrow}{} A$ then $\Pi_N(x) \to 1$; if it is $B \overset{\leftarrow\leftarrow}{} A$ then $\Pi_N(x) \to 0$, for every $x \in (0,1)$.
2. *(Coexistence, $R(0) > 1 > R(1)$.)* $\Pi_N(x) \to 0$ if $L(1) > 0$ and $\Pi_N(x) \to 1$ if $L(1) < 0$. Hence for large $N$ the scenario is $B \overset{\rightarrow\leftarrow}{\Leftarrow\Leftarrow} A$ when $L(1) > 0$ and $B \overset{\rightarrow\leftarrow}{\Rightarrow\Rightarrow} A$ when $L(1) < 0$; the crossing scenario $B \overset{\rightarrow\leftarrow}{\Rightarrow\Leftarrow} A$ is ruled out unless $L(1) = 0$.
3. *(Coordination, $R(0) < 1 < R(1)$.)* Let $x^* \in (0,1)$ be the root of $R(x^*) = 1$, the maximizer of $L$. Then $\Pi_N(x) \to 0$ for $x < x^*$ and $\Pi_N(x) \to 1$ for $x > x^*$, and

$$
\rho_A = \Theta\big(N^{-1/2} e^{-N L(x^*)}\big), \qquad \rho_B = \Theta\big(N^{-1/2} e^{-N(L(x^*) - L(1))}\big).
$$

   The source (Theorem 4, (43)–(46), with $q$ from Proposition 5, (37)) prints explicit constants: $\Pi_N(x)\sim\Theta_N(x)$ with a factor $e^{-w(q(x)-q(x^*))}$, $\rho_A\sim(R'(x^*)/(2\pi R(0)N))^{1/2}e^{-wq(x^*)}e^{-NL(x^*)}$ and $\rho_B\sim(R'(x^*)R(1)/(2\pi N))^{1/2}e^{-w(q(x^*)-q(1))}e^{-N(L(x^*)-L(1))}$. This page states only the exponential order because those constants are not right as printed: the source's own (31), Theorems 2–3 and $Q(x^*)=\tfrac12\log R(0)-wq(x^*)$ give $e^{+wq(x^*)}$ and $e^{+w(q(x^*)-q(1))}$ (an exact computation from the source's (11) with $a=4$, $b=1$, $c=2$, $d=3$, $w=1$ agrees with the "+" sign), and for $0<w<1$ the $q$ of (37) is not the limit of $N(\ell_{[Nx]}-L(x))$.

   Consequently, for large $N$ the coordination scenarios $B \overset{\leftarrow\rightarrow}{\Rightarrow\Rightarrow} A$ and $B \overset{\leftarrow\rightarrow}{\Leftarrow\Leftarrow} A$ are ruled out: both mutants are exponentially disfavoured relative to $1/N$, leaving only $B \overset{\leftarrow\rightarrow}{\Leftarrow\Rightarrow} A$.

## Depends on

- [Graph shapes of the fixation probability in each evolutionary scenario of the two-strategy Moran game](graph-shapes-of-the-fixation-probability-in-each-evolutionary-scenario.md)

## Expansion

From the recursion $d_{i+1} = r_i^{-1} d_i$, $\pi_i = \big(\sum_{j<i} \prod_{k \le j} r_k^{-1}\big)/s_N$ with $s_N = 1 + \sum_{j=1}^{N-1} \prod_{k=1}^j r_k^{-1}$, and $\log \prod_{k \le j} r_k^{-1} = N\ell_j$ with $\ell_j \approx L(j/N)$. A refinement of the Riemann-sum approximation shows that $N(\ell_{[Nx]} - L(x))$ is bounded uniformly in $x\in[0,1]$ and $N$ (each $r_k$ differs from $R(k/N)$ by $O(1/N)$, and the Riemann-sum error of the smooth $\log R$ is $O(1/N)$), so $\prod_{k\le[Nx]}r_k^{-1}=\Theta(e^{NL(x)})$. In the coordination case $L$ has an interior maximum at $x^*$ with $L''(x^*) = -R'(x^*)/R(x^*) = -R'(x^*) < 0$, so Laplace's method gives $s_N = \Theta(N^{1/2} e^{N L(x^*)})$, from which $\rho_A = 1/s_N$ and the limits of $\Pi_N$ follow (the partial sums up to $[Nx]$ are $O(N e^{NL(x)})$ when $x<x^*$, exponentially smaller than $s_N$, and the tail beyond $[Nx]$ is exponentially smaller when $x>x^*$); $\rho_B$ follows by the duality $A \leftrightarrow B$, $(a,b,c,d) \mapsto (d,c,b,a)$, $x \mapsto 1 - x$. In the coexistence case $L$ has an interior minimum and the sums are dominated by an endpoint, decided by the sign of $L(1)$.

## Sources

- E. P. Souza, E. M. Ferreira, A. G. M. Neves, "Fixation probabilities for the Moran process in evolutionary games with two strategies: graph shapes and large population asymptotics", arXiv:1805.00117 (2018): Hypothesis 1 (Section 2), Section 4 (definitions of $R$ and $L$), Section 5 (Proposition 5, Theorems 2–4, Corollary 1), Section 6 (Theorems 5 and 6). <https://doi.org/10.48550/arXiv.1805.00117> Published version: Journal of Mathematical Biology 78 (2019) 1033–1065, <https://doi.org/10.1007/s00285-018-1300-4>.
