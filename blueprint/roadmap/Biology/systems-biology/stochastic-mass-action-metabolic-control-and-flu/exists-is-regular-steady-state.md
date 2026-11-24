# Regular steady states exist by the implicit function theorem

Let $M$ and $R$ be finite index sets, $N \in \mathbb{R}^{M \times R}$ a stoichiometric matrix,
$f_i \colon \mathbb{R}^M \to \mathbb{R}$ rate laws that are continuously differentiable at
$s_0 \in \mathbb{R}^M$, and $e_0 \in \mathbb{R}^R$. Suppose $s_0$ is a steady state,
$N v(e_0, s_0) = 0$ with $v_i(e, s) = e_i f_i(s)$, and that the linear map
$\delta \mapsto N \bigl(e_{0,i}\, D f_i(s_0)\, \delta\bigr)_{i \in R}$ on $\mathbb{R}^M$ is injective.
Then there is a map $\sigma \colon \mathbb{R}^R \to \mathbb{R}^M$ with $\sigma(e_0) = s_0$ that is a
[regular steady state](is-regular-steady-state.md) at $e_0$.
