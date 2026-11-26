# Linear system for first-order weak-selection fixation probabilities

In the replacement process of [the setup](reproductive-value-and-neutral-fixation.md), with reproductive values
$\pi_1, \dots, \pi_N$ and neutral replacement law $p^\circ$, write $x_I = \prod_{k \in I} x_k$ for
$I \subseteq \{1, \dots, N\}$. Suppose the weak-selection derivatives of the marginal replacement
probabilities are multilinear polynomials of degree at most $D$ in $x \in \mathbb{B}^N$:

$$\left.\frac{d}{d\delta} e_{ji}(x)\right|_{\delta=0} = \sum_{I \subseteq \{1,\dots,N\},\, |I| \le D} c_I^{ji} x_I \qquad (1 \le i, j \le N).$$

Then for every transient initial state $\xi \in \mathbb{B}_T^N$, the fixation probability of allele $A$
satisfies

$$\rho_A(\xi) = \hat\xi + \delta \sum_{i=1}^N \pi_i \sum_{j=1}^N \sum_{I \subseteq \{1,\dots,N\},\, |I| \le D} c_I^{ji} \bigl(\eta_{\{i\} \cup I}^\xi - \eta_{\{j\} \cup I}^\xi\bigr) + O(\delta^2),$$

where $(\eta_I^\xi)_{1 \le |I| \le D + 1}$ is the unique solution of the finite linear system

$$\eta_I^\xi = \hat\xi - \xi_I + \sum_{(R,\alpha)} p^\circ(R, \alpha)\, \eta_{\tilde\alpha(I)}^\xi \quad (1 \le |I| \le D + 1), \qquad \sum_{i=1}^N \pi_i \eta_{\{i\}}^\xi = 0,$$

with $\tilde\alpha(I) = \{\tilde\alpha(i) : i \in I\}$. The solution is $\eta_I^\xi = \langle \hat x - x_I \rangle_\xi^\circ$,
in terms of the neutral sojourn-time operator.

## Depends on

- [Reproductive values and neutral fixation probability](reproductive-value-and-neutral-fixation.md)
- [Sojourn times as the rare-mutation derivative of the stationary distribution](sojourn-times-as-rare-mutation-derivative.md)
- [First-order weak-selection expansion of fixation probability](weak-selection-fixation-probability-expansion.md)

## Expansion

1. Substituting the multilinear expansion into
   $\widehat\Delta_{\mathrm{sel}}(x) = \sum_{i,j} \pi_i e_{ji}(x)(x_j - x_i)$ and using
   $x_I x_k = x_{I \cup \{k\}}$ on $\mathbb{B}^N$ writes its $\delta$-derivative as a combination of
   $x_{\{j\} \cup I} - x_{\{i\} \cup I} = (\hat x - x_{\{i\} \cup I}) - (\hat x - x_{\{j\} \cup I})$, functions
   vanishing at $\mathbf{A}$ and $\mathbf{B}$; the first-order expansion then gives the formula with
   $\eta_I^\xi = \langle \hat x - x_I \rangle_\xi^\circ$.
2. For $\phi$ vanishing at $\mathbf{A}$ and $\mathbf{B}$, $\langle \phi \rangle_\xi^\circ = \phi(\xi) + \sum_{(R,\alpha)} p^\circ(R,\alpha) \langle \phi \circ \tilde\alpha \rangle_\xi^\circ$, where $(\phi \circ \tilde\alpha)(x) = \phi(x_{\tilde\alpha})$. Since $\hat x$ is a neutral martingale and $(x_{\tilde\alpha})_I = x_{\tilde\alpha(I)}$, this gives the recurrence; the normalization holds because $\sum_i \pi_i (\hat x - x_i) = 0$.
3. Uniqueness: the recurrence is $(I - C)\eta = b$, with $C$ the transition matrix of the neutral ancestral-set chain $I \mapsto \tilde\alpha(I)$ on nonempty sets of size at most $D + 1$. Singletons map to singletons, and by the Fixation Axiom the singleton $\{i\}$ of the axiom is reachable from every nonempty set, so this chain has a unique closed communicating class, contained in the singletons (not necessarily all of them), with stationary law $\pi$ on it. A vector $h$ with $Ch = h$ is constant on that class, and since every state reaches it, $h$ equals that constant everywhere; so $\ker(I - C)$ is spanned by the constant vector, which the normalization $\sum_i \pi_i = 1$ excludes.

## Sources

- A. McAvoy and B. Allen, "Fixation probabilities in evolutionary dynamics under weak selection", Journal of Mathematical Biology 82 (2021), 14, <https://doi.org/10.1007/s00285-021-01568-4>. (Theorem 2, Lemma 1 and Eqs. 6, 35a–35b.)
