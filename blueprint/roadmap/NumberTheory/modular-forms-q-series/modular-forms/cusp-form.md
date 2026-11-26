# Cusp form

Let $\Gamma$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$ and $k \in \mathbb{Z}$. For
$g = \begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \mathrm{GL}_2(\mathbb{R})$ and a function
$f$ on the upper half-plane $\mathfrak{H}$, the weight-$k$ slash action is
$(f \mid_k g)(z) = \sigma_g\bigl(f(g \cdot z)\bigr)\, |\det g|^{k-1} (c z + d)^{-k}$, where $\sigma_g$ is the
identity when $\det g > 0$ and complex conjugation when $\det g < 0$, and
$g \cdot z = \sigma_g\bigl((a z + b)/(c z + d)\bigr)$ is the action of $\mathrm{GL}_2(\mathbb{R})$ on $\mathfrak{H}$,
which goes through $\bar z$ when $\det g < 0$. A **cusp form** of weight $k$
for $\Gamma$ is a holomorphic function $f \colon \mathfrak{H} \to \mathbb{C}$ with $f \mid_k \gamma = f$ for
every $\gamma \in \Gamma$ that vanishes at every cusp of $\Gamma$. They form a complex vector space
$S_k(\Gamma)$. A subgroup of $\mathrm{SL}_2(\mathbb{Z})$, such as [$\Gamma_0(N)$](congruence-subgroup-gamma0.md)
or [$\Gamma_1(N)$](congruence-subgroup-gamma1.md), is viewed in $\mathrm{GL}_2(\mathbb{R})$ through its
image.

In Mathlib this is [`CuspForm`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/NumberTheory/ModularForms/Basic.lean#L88 "CuspForm"), whose
fields are the invariance, holomorphy (`holo'`) and vanishing at every cusp `c` with `IsCusp c Γ`
(`zero_at_cusps'`).

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §0, p. 523 (the space
  $S_k(\Gamma)$ of holomorphic cusp forms of weight $k$ with respect to $\Gamma$).
