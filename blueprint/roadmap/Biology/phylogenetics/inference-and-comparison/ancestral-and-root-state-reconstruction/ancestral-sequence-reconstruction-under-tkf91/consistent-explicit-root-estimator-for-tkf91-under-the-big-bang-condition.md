# Consistent explicit root estimator for TKF91 under the big bang condition

**Setting.** Let $\{T^k\}_k$ be rooted trees with edge lengths and common root $\rho$, and let $\partial T$ denote the leaf set. Assume the taxon-rich setting:

1. *Nested:* $T^{k-1}$ is the restriction of $T^k$ to a subset of its leaves.
2. *Bounded height:* $h^* := \sup_k \max_{x \in \partial T^k} \ell_x < \infty$, where $\ell_x$ is the distance from $\rho$ to $x$.
3. *Big bang:* for every $s > 0$, the truncation $T^k(s) = \{\gamma : \ell_\gamma \le s\}$ satisfies $|\partial T^k(s)| \to \infty$ as $k \to \infty$.

Run the TKF91 insertion–deletion–substitution process on $T^k$ (rates $\nu$, $\lambda < \mu$, nucleotide law $\pi$), started from its stationary law $\Pi$ at the root, and observe the leaf sequences $\vec{X}_{\partial T^k}$.

**Estimator $F_{k,s}$.** Fix $s \in (0,h^*)$ and let $m = |\partial T^k(s)|$.

1. *Restriction.* Below each of the $m$ points of $\partial T^k(s)$, pick one leaf. The resulting $m$ leaves are nearly conditionally independent given the root.
2. *Length.* Round the average of $|\vec{X}_v| e^{(\mu-\lambda)h^*} - \frac{\lambda}{\mu-\lambda}\bigl(e^{(\mu-\lambda)h^*} - 1\bigr)$ over these leaves to the nearest integer. Call the result $\widehat{M}$.
3. *Sequence.* Average the first-nucleotide probabilities $p^\sigma_{\vec{X}_v}(t_j)$ over the chosen leaves, for $t_j = j$, $1 \le j \le \widehat{M}$. Subtract the known $\pi_\sigma$ terms to get a matrix $U$. Set the $i$-th root site to a maximizer over $\sigma$ of $(V^{-1}\Psi^{-1}U)_{i\sigma}$, where $V$ and $\Psi$ are the Vandermonde and diagonal matrices of the explicit inversion formula.

**Theorem.** Under the taxon-rich assumptions:

1. *(Consistency.)* For any $s_k \downarrow 0$, the estimators $F_k = F_{k,s_k}$ satisfy $\lim_{k\to\infty}\mathbb{P}\bigl[F_k(\vec{X}_{\partial T^k}) = \vec{X}_\rho\bigr] = 1$.
2. *(Error bound.)* For every $\epsilon > 0$ there are constants $C_1, C_2, C_3 > 0$ such that, for all $s \in (0, h^*/2]$ and $k \ge 1$,

$$ \mathbb{P}^{\Pi}\bigl[F_{k,s}(\vec{X}_{\partial T^k}) \ne \vec{X}_\rho\bigr] \le \epsilon + C_1 \exp\bigl(-C_2 |\partial T^k(s)|\bigr) + C_3 s. $$

Started from a fixed root sequence $\vec{x}$ of length $M$, the error is at most $\exp(-|\partial T^k(s)|/\hat C_1^M) + \hat C_2^M(1 + \max_\sigma \pi_\sigma^2)\, s$ (Theorem 3).

## Proof depends on

- [Constructive initial-state identifiability of the TKF91 process](constructive-initial-state-identifiability-of-the-tkf91-process.md)

## Expansion

The big bang condition is known to be necessary and sufficient for consistent root reconstruction for such Markov models on bounded-height nested trees; earlier existence proofs were not constructive. Here the estimator is explicit and runs in polynomial time. The $m$ selected leaves branch off within distance $s$ of the root, and the effect of their shared ancestry above level $s$ costs a probability of order $\delta^{-2}(M+1)s$ for deviations of size $\delta$ (Lemmas 4 and 5). Concentration of averages of $m$ bounded variables then makes the empirical length and first-nucleotide averages close to their expectations, with exponentially small error in $m$.

Proposition 1 bounds the length error by $2e^{-C_1 m} + C_2(M+1)s$. Proposition 2 bounds the sequence error by $8M e^{-m/(8\hat C)} + C M^2 \hat C s$, with $\hat C = \|V^{-1}\Psi^{-1}\|_{\infty\to\infty}^2$. Given these, applying the [explicit inversion formulas](constructive-initial-state-identifiability-of-the-tkf91-process.md) and rounding recovers the root exactly. Averaging over the stationary root law, and truncating at large $M$ to absorb $\epsilon$, gives the stated bound. Letting $k \to \infty$ and then $s \to 0$ gives consistency.

## Sources

- W.-T. L. Fan and S. Roch, "Statistically consistent and computationally efficient inference of ancestral DNA sequences in the TKF91 model under dense taxon sampling", arXiv:1707.05711 (2017), <https://doi.org/10.48550/arXiv.1707.05711>. Assumption 1 (taxon-rich setting), Section 2 (root reconstruction algorithm), Theorem 1 (consistency), Theorem 2 (error bound), Theorem 3 (pointwise error bound), Propositions 1–2. Published version: Bulletin of Mathematical Biology 82 (2020) 21, <https://doi.org/10.1007/s11538-020-00693-3>.
