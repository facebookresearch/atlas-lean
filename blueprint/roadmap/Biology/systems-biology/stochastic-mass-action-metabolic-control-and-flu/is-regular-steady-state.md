# Regular steady state of a metabolic network

Let $M$ (metabolites) and $R$ (reactions) be index sets with $R$ finite, let $N \in \mathbb{R}^{M \times R}$ be a stoichiometric matrix, $f_i \colon \mathbb{R}^M \to \mathbb{R}$
rate laws with [fluxes](flux.md) $v_i(e, s) = e_i f_i(s)$, $\sigma \colon \mathbb{R}^R \to \mathbb{R}^M$ and
$e_0 \in \mathbb{R}^R$. Then $\sigma$ is a regular steady state at $e_0$ when:

- $\sigma$ is differentiable at $e_0$, and every $f_i$ is differentiable at $\sigma(e_0)$;
- $N v(e, \sigma(e)) = 0$ for all $e$ in a neighbourhood of $e_0$;
- the linear map $\delta \mapsto N \bigl(e_{0,i}\, D f_i(\sigma(e_0))\, \delta\bigr)_{i \in R}$ on
  $\mathbb{R}^M$ is injective (for finite $M$ it is square, so this is its invertibility).
