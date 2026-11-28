# Low equivalence of stores

Security levels are Booleans, with $\mathrm{false}$ low (public) and $\mathrm{true}$ high (secret). For a policy $\Gamma : \mathbb{N} \to \mathrm{Bool}$ assigning a level to each variable and two IMP stores $s, t : \mathbb{N} \to \mathbb{N}$, $s$ and $t$ are low-equivalent when they agree on every public variable:

$$\forall x,\ \Gamma(x) = \mathrm{false} \implies s(x) = t(x).$$
