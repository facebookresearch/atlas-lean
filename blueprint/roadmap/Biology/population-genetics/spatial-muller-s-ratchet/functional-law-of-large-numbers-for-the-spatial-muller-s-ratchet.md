# Functional law of large numbers for the spatial Muller's ratchet

**Model.** Particles live on the rescaled lattice $L_N^{-1}\mathbb{Z}$ and perform symmetric nearest-neighbour random walks at total jump rate $m_N$. Each particle carries a mutation count $k \in \mathbb{N}_0$ and fitness $s_k$. With $u$ the local density of all particles, a particle with $k$ mutations reproduces at per-capita rate $q_+(u)s_k$ and dies at rate $q_-(u)$; at each birth the offspring gains one extra mutation with probability $\mu$. Let $u^N_k(t)$ be the rescaled empirical density (mass $1/N$ per particle) of type-$k$ particles.

**Hypotheses.**
1. $m_N/L_N^2 \to m \in (0,\infty)$ and $L_N = \Theta(N)$.
2. $s_0 = 1$, $s_k \ge 0$, $(s_k)$ non-increasing, $s_k \to 0$.
3. $q_+, q_- : [0,\infty) \to [0,\infty)$ are polynomials with $\deg q_+ < \deg q_-$ (density regulation).
4. The initial densities $f = (f_k) : \mathbb{R} \to \ell_1^+$ are a.e. continuous and essentially bounded in $\ell_1$.

**Theorem.** As $N \to \infty$, $u^N$ converges in distribution in the Skorokhod $J_1$ topology to a deterministic process whose type-$k$ components have Lebesgue densities $u_k(t,x)$ forming a non-negative mild solution, locally bounded in $\ell_1$, of the infinite reaction-diffusion system

$$\partial_t u_k = \frac{m}{2}\Delta u_k + F_k(u), \qquad u(0,\cdot) = f, \qquad k \in \mathbb{N}_0,$$

$$F_k(u) = q_+(\|u\|_{\ell_1})\bigl(s_k(1-\mu)u_k + \mathbf{1}_{\{k\ge 1\}} s_{k-1}\mu\, u_{k-1}\bigr) - q_-(\|u\|_{\ell_1})\,u_k .$$

**Long-time profile.** If in addition the reaction term is monostable ($s_k$ strictly decreasing, $\mu \in (0,1)$, $q_+ \ge q_-$ on $[0,1]$ with further positivity conditions), then on any compact interval the mass ratios $u^N_k(T)/u^N_0(T)$ are, with high probability for large $T$ and then large $N$, pinned between explicit constants $\alpha_k (\mathfrak{Q}_{\min}/\mathfrak{Q}_{\max})^k$ and $\alpha_k(\mathfrak{Q}_{\max}/\mathfrak{Q}_{\min})^k$ set by the mutation-selection balance of the reaction term.

## Depends on

- [Almost-sure repeated clicking of a finite mutation ratchet](../mutation-selection-balance/muller-s-ratchet-model-and-almost-sure-clicking.md)

## Expansion

Diffusive scaling of the random walks ($m_N/L_N^2 \to m$) gives the Laplacian, and the large local carrying capacity ($L_N = \Theta(N)$ particles per unit length at density one) makes birth-death noise vanish, so the limit is deterministic. The polynomial degree gap gives uniform moment bounds on the total mass, which yields tightness; identifying limit points uses the martingale problem tested against the discrete heat semigroup, so solutions are obtained in the variation-of-constants (mild) sense. Unlike the well-mixed ratchet, the deterministic limit never loses the fittest class: in the bulk behind an expanding front the classes settle into a mutation-selection balance, which is what the long-time comparison quantifies.

## Sources

- J. L. de Oliveira Madeira, M. Ortgiese, S. Penington, "A functional law of large numbers for a spatial model of Muller's ratchet" (2026), Assumptions 1-4, Theorem 2.1, Definition 2.3 and Theorem 2.4, <https://doi.org/10.48550/arXiv.2603.06478>.
