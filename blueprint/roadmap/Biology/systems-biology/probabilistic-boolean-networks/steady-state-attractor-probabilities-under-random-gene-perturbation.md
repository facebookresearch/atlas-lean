# Steady-state attractor probabilities under random gene perturbation

**Setting.** Let $f : \{0,1\}^n \to \{0,1\}^n$ be a Boolean network with attractors $A_1, \dots, A_m$ and basins $B_1, \dots, B_m$ (so $A_k \subseteq B_k$ and the basins partition $\{0,1\}^n$). In the Boolean network with perturbation (BNp) each step is, with probability $b = (1-p)^n$, the update $x \mapsto f(x)$, and otherwise a perturbation $x \mapsto x \oplus \gamma$ with a nonzero flip pattern. For $0 < p < 1$ the chain has a unique stationary law $\pi$; write $\pi(B) = \sum_{x \in B}\pi(x)$. Let

$$P^*_y(x) = \frac{p^{\eta(x,y)}(1-p)^{n-\eta(x,y)}}{1 - (1-p)^n}, \qquad x \ne y,$$

be the probability of landing at $x$ from $y$ given that a perturbation occurs, let $\pi^*(y \mid B_i)$ be the long-run probability of being at $y$ just before a perturbation, conditioned on being in $B_i$, and let $\delta(x, A_k)$ be the number of iterations of $f$ needed to reach $A_k$ from $x \in B_k$.

**Theorem 1 (basin probabilities).** With $P^*_{B_i B_k} = \sum_{x \in B_k}\sum_{y \in B_i} P^*_y(x)\, \pi^*(y \mid B_i)$,

$$\pi(B_k) = \sum_{i=1}^m P^*_{B_i B_k}\, \pi(B_i), \qquad k = 1, \dots, m,$$

i.e. $(\pi(B_1), \dots, \pi(B_m))$ is the stationary law of the $m$-state chain of basin-to-basin jumps at perturbation times.

**Theorem 2 (attractor probabilities).**

$$\pi(A_k) = \sum_{i=1}^m \sum_{x \in B_k} \sum_{y \in B_i} P^*_y(x)\, \pi^*(y \mid B_i)\, (1-p)^{n\,\delta(x, A_k)}\, \pi(B_i).$$

**Small-$p$ approximation.** Between perturbations the system almost surely sits on an attractor, so $\pi^*(y \mid B_i) \approx \mathbf{1}[y \in A_i]/|A_i|$, giving

$$P^*_{B_i B_k} \approx \frac{1}{|A_i|}\sum_{x \in B_k}\sum_{y \in A_i} P^*_y(x), \qquad \pi(A_k) \approx \sum_{i=1}^m \frac{\pi(B_i)}{|A_i|} \sum_{x \in B_k}\sum_{y \in A_i} P^*_y(x)\, (1-p)^{n\,\delta(x, A_k)}.$$

Thus long-run attractor (phenotype) probabilities are obtained from an $m \times m$ linear system instead of the full $2^n$-state chain.

## Expansion

Perturbation events occur independently of the state at each step with probability $1 - b$, so the state seen at perturbation times has the stationary law, and between perturbations the deterministic dynamics never leaves a basin; this gives Theorem 1 as a balance of basin occupancy across perturbation times. For Theorem 2, after a perturbation lands at $x \in B_k$ the trajectory reaches $A_k$ after $\delta(x, A_k)$ steps if no new perturbation occurs, and the number of steps until the next perturbation is geometric. The expected fraction of the inter-perturbation time spent in $A_k$ is $b^{\delta(x, A_k)}$, which is the identity $\sum_{j \ge \delta}(1-b) b^j = b^{\delta}$ (the source's Lemma 3); averaging over landing points (Lemma 2) gives the formula. The same three-step scheme (basin probabilities, attractor-given-basin probabilities, sum over networks in which a set is an attractor) extends to PBNs with several constituent networks by working on the pair (state, network).

## Depends on

- [Markov chain of a probabilistic Boolean network](markov-chain-of-a-probabilistic-boolean-network.md)

## Sources

- Y. Xiao, "A tutorial on analysis and simulation of Boolean gene regulatory network models", Current Genomics 10 (2009), 511–525, Section 3.2.1 (Eqs. (9)–(19), Theorems 1–2, Lemmas 1–3) and Section 3.2.2, <https://doi.org/10.2174/138920209789208237> (PMC2808677).
- M. Brun, E. R. Dougherty, I. Shmulevich, "Steady-state probabilities for attractors in probabilistic Boolean networks", Signal Processing 85 (2005), 1993–2013.
