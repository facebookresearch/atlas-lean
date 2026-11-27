# Robustly unsaturated boundary sets via Lyapunov exponents

**Model.** $m$ interacting species, species $i$ structured into $n_i$ classes (ages, stages or patches), $n = \sum_i n_i$. With row vectors $X^i_t \in \mathbb{R}_+^{n_i}$ and $X_t = (X^1_t, \dots, X^m_t)$,

$$
X^i_{t+1} = X^i_t A_i(X_t), \qquad \text{i.e.}\quad X_{t+1} = X_t A(X_t),\quad A = \operatorname{diag}(A_1, \dots, A_m),
$$

under: (H1) each $X \mapsto A_i(X)$ is continuous into nonnegative $n_i \times n_i$ matrices; (H2) each $A_i(X)$ has the fixed zero pattern of a primitive matrix $P_i$; (H3) dissipativity: there is a compact $S_A$ that every orbit eventually enters. Write $\Phi_A(x) = xA(x)$, $\|x^i\| = \sum_j x^{ij}$, and $S_0 = \{x : \prod_i \|x^i\| = 0\}$ for the extinction set.

**Growth rates.** For $X_0 = x$ let $r_i(x) = \limsup_{t\to\infty} \frac1t \log \|A_i(X_0) A_i(X_1) \cdots A_i(X_{t-1})\|$. For a $\Phi_A$-invariant probability $\mu$ the limit exists $\mu$-a.e. (subadditive ergodic theorem) and $r_i(\mu) = \int r_i\, d\mu$; for ergodic $\mu$, $r_i(x) = r_i(\mu)$ $\mu$-a.e. If species $i$ is present ($\|x^i\| > 0$) then $r_i(x) \le 0$.

**Perturbations.** A $\delta$-perturbation is a model $X_{t+1} = X_t A^\delta(X_t)$ satisfying (H1)–(H3) with $S_{A^\delta} \subset N_\delta(S_A)$ and $\|A(x) - A^\delta(x)\| \le \delta$ on $N_1(S_A)$. A compact $M \subset S_0$ is *unsaturated* if it is isolated in $\mathbb{R}_+^n$ and its stable set $W^s(M) = \{x : \omega(x) \subset M\}$ lies in $S_0$; it is *robustly unsaturated* if its continuations under all sufficiently small perturbations are unsaturated.

**Theorem.** Let $M$ be a compact isolated invariant set of $\Phi_A$ restricted to $S_0$. The following are equivalent, and each implies that $M$ is robustly unsaturated:

1. $\max_{1 \le i \le m} r_i(\mu) > 0$ for every invariant probability measure $\mu$ with $\mu(M) = 1$;
2. there are $p_1, \dots, p_m > 0$ with $\sum_i p_i r_i(\mu) > 0$ for every ergodic $\mu$ with $\mu(M) = 1$;
3. there are $p_1, \dots, p_m > 0$ with $\sum_i p_i r_i(x) > 0$ for all $x \in M$.

**Converse (necessity).** If $\Phi_A$ is $C^2$ and some ergodic $\mu$ supported on $M$ has $r_i(\mu) \le 0$ for every species $i$ absent from $\operatorname{supp}\mu$, then $M$ is not robustly unsaturated: for every $\delta > 0$ some $\delta$-perturbation has an orbit starting off $S_0$ whose $\omega$-limit lies in the continuation of $M$.

## Expansion

Condition 3 says that $P(x) = \prod_i \|x^i\|^{p_i}$ behaves like an average Lyapunov function near $M$. The proof of robustness argues by contradiction with empirical occupation measures $\Lambda_t(x) = \frac1t \sum_{s<t} \delta_{X_s}$: for an interior orbit, every weak$^*$ limit point of $\Lambda_t(x)$ is an invariant measure on the global attractor with $r_i(\mu) \le 0$ for all $i$. If interior orbits of $\delta_n$-perturbations with $\delta_n \to 0$ converged to continuations of $M$, limits of their saturated invariant measures would be saturated invariant measures of $\Phi_A$ supported on $M$, contradicting condition 1. Growth rates are handled on a trajectory-space extension where they become Lyapunov exponents of a cocycle.

## Sources

- G. Roth, P. L. Salceanu, S. J. Schreiber, "Robust permanence for ecological maps", arXiv:1603.05004 (2016): Section 2 (model, assumptions H1–H3, perturbations, Definitions 2.1–2.2), Section 3.1 (growth rates, Definition 3.1, Theorem 3.2, Proposition 3.4), Section 4 (proofs: trajectory space, Propositions 4.1, 4.3 and 4.10). <https://doi.org/10.48550/arXiv.1603.05004> Published version: SIAM Journal on Mathematical Analysis 49.5 (2017): 3527-3549, <https://doi.org/10.1137/16M1066440>.
