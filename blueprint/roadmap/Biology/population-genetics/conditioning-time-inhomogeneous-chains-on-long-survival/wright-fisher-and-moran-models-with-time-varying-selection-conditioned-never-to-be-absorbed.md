# Wright–Fisher and Moran models with time-varying selection conditioned never to be absorbed

**Wright–Fisher model.** A population of fixed size $n_0 \ge 3$ has two types $\mathsf{a}$ and $\mathsf{A}$; $X_n$ is the number of $\mathsf{a}$ individuals in generation $n$, with $X_0 \in \{1,\dots,n_0-1\}$. The selective advantage of $\mathsf{a}$ in generation $n$ is
$$\sigma_n = s_1 + \frac{s_2}{n} + \frac{s_3}{n^2} + O(n^{-3}),\qquad \sigma_n > -1,\ s_1 > -1,$$
and given $X_n = i$, $X_{n+1} \sim \mathrm{Bin}(n_0, p_n(i))$ with $p_n(i) = (1+\sigma_n)i/(n_0 + \sigma_n i)$. Killing the chain at the absorbing states $0$ and $n_0$ gives kernels $K_n$ on $\{1,\dots,n_0-1\}$ converging to the killed kernel $K$ with constant selection $s_1$, with
$$\frac{K_n(i,j)}{K(i,j)} = 1 + \frac{a(i,j)}{n} + O(n^{-2}),\qquad a(i,j) = s_2\Big(\frac{j}{1+s_1} - \frac{n_0 i}{n_0 + s_1 i}\Big).$$

**Moran model.** With the same $\sigma_n$, one individual is replaced per step: $i \to i+1$ with probability $\frac{n_0 - i}{n_0}\cdot\frac{(1+\sigma_n)i}{n_0 + \sigma_n i}$, $i \to i-1$ with probability $\frac{i}{n_0}\cdot\frac{n_0 - i}{n_0 + \sigma_n i}$, and otherwise $i$ is unchanged.

**Result.** For both models the general theory of time-inhomogeneous finite chains conditioned to survive applies: with $\lambda$ the Perron eigenvalue of the killed constant-selection kernel,
- the non-absorption probability satisfies $\mathbb{P}(X_k \notin \{0, n_0\},\ k \le n) \sim C(m,x_0)\,\lambda^{n}\,n^{\kappa}$ for an explicit exponent $\kappa$ (the stationary average of $a$ under the $h$-transformed chain);
- conditioning on non-absorption up to time $n$ and letting $n \to \infty$ yields a well-defined time-inhomogeneous Markov chain, the model conditioned never to be absorbed, given by a Doob transform with a space-time harmonic function;
- its one-step kernels approach the $h$-transform $Q$ of the constant-selection killed kernel at rate $O(n^{-1})$, its marginals approach the quasi-limiting law $\pi = LR$ at rate $O(n^{-1})$ in total variation, and its occupation frequencies converge almost surely to $\pi$.

The first-order correction vanishes, so that both rates improve to $O(n^{-2})$, exactly when $s_1 s_2 = 0$ for the Wright–Fisher model (then $a(i,j) = V(j) - V(i)$ with $V(i) = s_2 i$, $\kappa = 0$) and exactly when $s_2 = 0$ for the Moran model.

## Depends on

- [Doob transform limit of time-inhomogeneous finite Markov chains conditioned to survive](doob-transform-limit-of-time-inhomogeneous-chains-conditioned-to-survive.md)

## Expansion

Both killed kernels have full (Wright–Fisher) or tridiagonal (Moran) support independent of $n$, and a Taylor expansion of the binomial and Moran transition probabilities in $\sigma_n$ gives the $1/n$ and $1/n^2$ coefficients the general theory needs. The gradient criterion is checked on diagonal transitions: a constant $\kappa$ must equal $a(i,i)$ for every $i$, which is $-s_1 s_2 i(n_0 - i)/((1+s_1)(n_0 + s_1 i))$ for Wright–Fisher and $s_2$ times a non-constant function of $i$ for Moran, forcing $s_1 s_2 = 0$ and $s_2 = 0$ respectively. Under neutrality with constant selection this reduces to the classical Wright–Fisher and Moran chains conditioned on non-absorption, whose conditioned laws are given by the $h$-transform with the Perron eigenvector.

## Sources

- Kohki Iba, "Finite-State Time-Inhomogeneous Markov Chains Conditioned to Survive", arXiv:2610.38590 (2026), Section 3 (subsections on the time-inhomogeneous Wright–Fisher and Moran models conditioned never to be absorbed) and the two main theorems of Section 1.3, <https://doi.org/10.48550/arXiv.2610.38590>.
