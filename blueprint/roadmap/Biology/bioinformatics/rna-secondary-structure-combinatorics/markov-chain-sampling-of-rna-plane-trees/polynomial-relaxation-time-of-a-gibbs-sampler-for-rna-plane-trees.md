# Polynomial relaxation time of a Gibbs sampler for RNA plane trees

**Model.** Represent the branching structure of an RNA secondary structure by a plane (rooted, ordered) tree $t$ with $n$ edges. Let $d_0(t)$ be its number of leaves and $d_1(t)$ its number of non-root nodes of down-degree $1$. A simplified nearest-neighbor thermodynamic model assigns the energy $E(t) = \alpha\, d_0(t) + \beta\, d_1(t)$ with fixed real parameters $\alpha, \beta$, and the Gibbs distribution $\pi(t) = e^{-E(t)}/Z$ on the $C_n$ (Catalan) plane trees. Deutsch's bijection $\Phi$ maps plane trees with $n$ edges to 2-Motzkin paths of length $m = n-1$: words in $\{U,H,I,D\}$ in which no prefix has more $D$'s than $U$'s and the total numbers of $U$'s and $D$'s are equal. It satisfies $|x|_I = d_1(t)$ and $|x|_U + |x|_H + 1 = d_0(t)$ for $x = \Phi(t)$, so the Gibbs law transfers to 2-Motzkin paths with $E(x) = \alpha(|x|_U + |x|_H + 1) + \beta |x|_I$.

**Chain.** Each step of $\mathcal{M}$ picks one of four local moves uniformly at random, proposes a modified word, and accepts it with probability $1/2$ if it is a valid 2-Motzkin path (otherwise it stays put). The moves are:

1. Resample a consecutive pair $UD$ or $HH$ as $UD$ or $HH$, with probabilities proportional to $1$ and $e^{-\alpha}$.
2. Resample a single $H$ or $I$ as $H$ or $I$, with probabilities proportional to $e^{-\alpha}$ and $e^{-\beta}$.
3. Swap two (not necessarily adjacent) symbols that are both in $\{U,D\}$.
4. Transpose an adjacent pair $ab$ or $ba$ with $a \in \{U,D\}$ and $b \in \{H,I\}$.

$\mathcal{M}$ is ergodic and reversible with stationary distribution $\pi$.

**Theorem.** For all fixed $\alpha, \beta \in \mathbb{R}$, the relaxation time of $\mathcal{M}$ on 2-Motzkin paths of length $m$ satisfies

$$ \tau_{\mathrm{rel}}(\mathcal{M}) = \frac{1}{\mathrm{Gap}(\mathcal{M})} = O(m^7). $$

Since $\pi(x) \ge e^{-O(m)}/|\Omega|$ and $|\Omega| \le 4^m$, the standard bound $\tau(\varepsilon) \le \mathrm{Gap}^{-1}\log(1/(\pi_{\min}\varepsilon))$ gives a polynomial mixing time.

## Expansion

The proof bounds the spectral gap through four nested decompositions. The decomposition theorems used are Martin–Randall, $\mathrm{Gap}(P) \ge \tfrac12 \mathrm{Gap}(\bar P)\min_i \mathrm{Gap}(P_i)$, and Hermon–Salez, $\mathrm{Gap}(P) \ge \min\{\chi\, \mathrm{Gap}(\bar P), \min_i \mathrm{Gap}(P_i)\}$.

1. Split the state space by the number $k$ of $U$'s. The projection chain is a birth–death chain on $k$ with log-concave weights and has relaxation time $O(m^4)$ (Lemma 4.1).
2. Split by the pattern of $H$ and $I$ symbols. A coupling shows the projection mixes in $O(m\log m)$ (Lemma 4.2).
3. Split by the Dyck-path skeleton of $U$/$D$ steps. Comparison with the mountain–valley chain on Dyck paths gives relaxation time $O(m^2)$ (Lemma 4.3).
4. The innermost restrictions are isomorphic to adjacent transpositions on binary strings, with relaxation time $O(m^3)$ (Lemma 4.4).

Combining the four levels gives Theorem 4.5. The chain is a practical sampler for exploring how RNA branching statistics (numbers of hairpins and helix-continuing nodes) depend on the energy parameters.

## Sources

- A. Kirkpatrick and K. Patton, "Markov Chain-based Sampling for Exploring RNA Secondary Structure under the Nearest Neighbor Thermodynamic Model", arXiv:2004.01089 (2020), <https://doi.org/10.48550/arXiv.2004.01089>. Section 2 (plane trees, Deutsch's bijection), Section 3 (the chain), Theorems 2.4–2.5 (decomposition theorems), Lemmas 4.1–4.4, Theorem 4.5 (main mixing result). Published version: A. Kirkpatrick, K. Patton, P. Tetali, C. Mitchell, "Markov chain-based sampling for exploring RNA secondary structure under the nearest neighbor thermodynamic model and extended applications", Mathematical and Computational Applications 25 (2020) 67, <https://doi.org/10.3390/mca25040067>.
