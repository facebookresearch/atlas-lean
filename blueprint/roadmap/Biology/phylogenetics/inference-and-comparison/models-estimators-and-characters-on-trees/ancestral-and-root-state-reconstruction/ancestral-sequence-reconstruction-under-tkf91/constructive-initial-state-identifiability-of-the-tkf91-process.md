# Constructive initial-state identifiability of the TKF91 process

**Model.** The TKF91 edge process $(\mathcal{I}_t)_{t \ge 0}$ is a continuous-time Markov process on DNA sequences preceded by an immortal link $\bullet$. Its parameters are a substitution rate $\nu > 0$, an insertion rate $\lambda$ and a deletion rate $\mu$ with $0 < \lambda < \mu$, and a stationary nucleotide law $\pi = (\pi_A,\pi_T,\pi_C,\pi_G)$. Each nucleotide is substituted at rate $\nu$ by a draw from $\pi$ and deleted at rate $\mu$. Each site, the immortal link included, inserts a new $\pi$-distributed nucleotide immediately to its right at rate $\lambda$. Write $\gamma = \lambda/\mu$, $\beta_t = e^{-(\mu-\lambda)t}$ and

$$ \eta(t) = \frac{1 - e^{(\lambda-\mu)t}}{1 - \gamma e^{(\lambda-\mu)t}}, $$

the probability that a given nucleotide has died by time $t$ and left no descendant.

**Lemma (explicit inversion formulas).** Fix $h \ge 0$.

1. *Length.* Started from a sequence of length $M$, the expected length satisfies

$$ \mathbb{E}_M\bigl[|\mathcal{I}_h|\bigr] = M\beta_h + \frac{\gamma(1-\beta_h)}{1-\gamma}, $$

so $M \mapsto \mathbb{E}_M[|\mathcal{I}_h|]$ is injective, with inverse $z \mapsto \beta_h^{-1}\bigl(z - \gamma(1-\beta_h)/(1-\gamma)\bigr)$.

2. *Sequence.* For a root sequence $\vec{x} = (x_1,\dots,x_M)$, the probability that the first nucleotide at time $t$ is $\sigma$ is

$$ p^{\sigma}_{\vec{x}}(t) = \pi_\sigma \phi(t)\bigl[1 - \eta(t)^M\bigr] + \psi(t)\sum_{i=1}^{M} \mathbf{1}_{\{x_i = \sigma\}}\, \eta(t)^{i-1} + \pi_\sigma \gamma\, \eta(t), $$

with explicit functions $\phi$ and $\psi(t) = (1-\gamma\eta(t))e^{-(\mu+\nu)t} > 0$. For distinct times $0 \le t_1 < \dots < t_M$, the map $\vec{x} \mapsto \bigl(p^\sigma_{\vec{x}}(h + t_j)\bigr)_{\sigma, j}$ is injective. Indeed, subtracting the known $\pi_\sigma$ terms leaves the matrix equation $H = \Psi V Y^{\vec{x}}$. Here $\Psi = \mathrm{diag}(\psi(h+t_j))$, $V$ is the Vandermonde matrix with entries $\eta(h+t_j)^{i-1}$, and $Y^{\vec{x}}_{i\sigma} = \mathbf{1}_{\{x_i = \sigma\}}$. So $Y^{\vec{x}} = V^{-1}\Psi^{-1}H$.

## Expansion

The length formula comes from the linear ODE $\frac{d}{dt}\mathbb{E}_M|\mathcal{I}_t| = -(\mu-\lambda)\mathbb{E}_M|\mathcal{I}_t| + \lambda$: each nucleotide dies at rate $\mu$, and each of the $|\mathcal{I}_t| + 1$ sites (immortal link included) inserts at rate $\lambda$. The first-nucleotide formula decomposes on which ancestral site produced the first surviving nucleotide. The $i$-th root nucleotide contributes only if nucleotides $1,\dots,i-1$ left no descendants (probability $\eta^{i-1}$) and it survived unsubstituted (factor $\psi$). The other terms come from inserted nucleotides, which are $\pi$-distributed. Since the $\eta(h+t_j)$ are distinct, $V$ is invertible.

The point of the lemma is that the inverse is explicit and linear in observable averages. Replacing the expectations by empirical averages over many nearly independent leaves gives a computable root estimator; this is the consistent explicit root estimator for TKF91 under the big bang condition.

## Sources

- W.-T. L. Fan and S. Roch, "Statistically consistent and computationally efficient inference of ancestral DNA sequences in the TKF91 model under dense taxon sampling", arXiv:1707.05711 (2017), <https://doi.org/10.48550/arXiv.1707.05711>. Definition 1 (TKF91 edge process), Lemma 1 (distribution of the first nucleotide), Lemma 2 (constructive initial-state identifiability), Section 3. Published version: Bulletin of Mathematical Biology 82 (2020) 21, <https://doi.org/10.1007/s11538-020-00693-3>.
