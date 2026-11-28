# Action values are linear in a linear MDP

In a linear MDP every policy has linear action-value functions: $Q^\pi_h(x,a) = \langle \phi(x,a), w^\pi_h \rangle$ with $w^\pi_h = \theta_h + \int V^\pi_{h+1}\, d\mu_h$. Under the integrated normalization of $\mu_h$ the weights also satisfy $\lVert w^\pi_h \rVert_2 \le 2H\sqrt d$.

**Statement.** Let $(\mathcal{S}, \mathcal{A}, H, \mathbb{P}, r)$ be a [linear MDP](linear-mdp.md) with feature map $\phi$, measures $\mu_h$ and reward vectors $\theta_h$, and rewards in $[0,1]$. Let $\pi = (\pi(\cdot, h))_{h \in [H]}$ be a policy mapping states and steps to actions, with values

$$
V^\pi_h(x) = \mathbb{E}\Big[\sum_{h'=h}^{H} r_{h'}(x_{h'}, \pi(x_{h'}, h')) \,\Big|\, x_h = x\Big], \qquad Q^\pi_h = r_h + \mathbb{P}_h V^\pi_{h+1}, \qquad V^\pi_{H+1} \equiv 0 .
$$

1. (Linearity.) For every $h \in [H]$ the vector

$$
w^\pi_h = \theta_h + \int_{\mathcal{S}} V^\pi_{h+1}(x')\, d\mu_h(x') \in \mathbb{R}^d
$$

satisfies $Q^\pi_h(x,a) = \langle \phi(x,a), w^\pi_h \rangle$ for all $(x,a)$.

2. (Weight bound.) If in addition $\lVert \theta_h \rVert_2 \le \sqrt d$ and the integrated normalization $\lVert \int g\, d\mu_h \rVert_2 \le \sqrt d$ holds for every measurable $g : \mathcal{S} \to [0,1]$, then $\lVert w^\pi_h \rVert_2 \le 2H\sqrt d$ for every $h$.

The first part concerns the action-value functions of every policy, so it uses the linearity of the transition kernel, not only of one value function. Jin et al. state the weight bound (their Lemma B.1) under the total-mass normalization $\lVert \mu_h(\mathcal{S}) \rVert_2 \le \sqrt d$. Its proof uses the integrated form, as Agarwal, Kakade, Krishnamurthy and Sun record, and part 2 is stated under that form.

## Depends on

- [Linear MDP](linear-mdp.md)

## Proof depends on

None.

## Expansion

By the Bellman equation for $\pi$, $Q^\pi_h(x,a) = r_h(x,a) + \int V^\pi_{h+1}(x')\, \mathbb{P}_h(dx' \mid x,a) = \langle \phi(x,a), \theta_h \rangle + \int V^\pi_{h+1}(x') \langle \phi(x,a), d\mu_h(x') \rangle$, which is $\langle \phi(x,a), w^\pi_h\rangle$. For the norm, $0 \le V^\pi_{h+1} \le H$, so applying the integrated normalization to $g = V^\pi_{h+1}/H$ gives $\lVert \int V^\pi_{h+1}\, d\mu_h \rVert_2 \le H \sqrt d$. With $\lVert \theta_h \rVert_2 \le \sqrt d$ this gives $\lVert w^\pi_h \rVert_2 \le \sqrt d + H\sqrt d \le 2H\sqrt d$.

A complete expansion needs a page for the finite-horizon policy Bellman equation $Q^\pi_h = r_h + \mathbb{P}_h V^\pi_{h+1}$ on a measurable state space.

## Sources

- C. Jin, Z. Yang, Z. Wang and M. I. Jordan, "Provably Efficient Reinforcement Learning with Linear Function Approximation", Conference on Learning Theory (COLT 2020), PMLR 125; journal version Mathematics of Operations Research 48(3):1496–1521, 2023, doi:10.1287/moor.2022.1309. Numbers from arXiv:1907.05388v2: Proposition 2.3 (proof in Appendix A) and Lemma B.1 with its proof. <https://arxiv.org/abs/1907.05388v2>
- A. Agarwal, S. Kakade, A. Krishnamurthy and W. Sun, "FLAMBE: Structural Complexity and Representation Learning of Low Rank MDPs", Advances in Neural Information Processing Systems 33 (NeurIPS 2020). Numbers from arXiv:2006.10814v2: Definition 1 and its footnote, which attributes the integrated normalization to the proof of Jin et al.'s Lemma B.1. <https://arxiv.org/abs/2006.10814v2>
