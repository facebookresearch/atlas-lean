# Inverse associator of the disjoint-union tensor as a pairing

In the category of sets and relations with the disjoint union as tensor, let $\pi_1 : A \sqcup B \to A$ and $\pi_2 : A \sqcup B \to B$ be the [projection relations](fst.md), relating $\mathrm{inl}(a)$ to $a$ and $\mathrm{inr}(b)$ to $b$, and let $\langle f, g\rangle$ be the [pairing](pair.md) of relations into a disjoint union. Composition is written in forward order, $f \,;\, g$ meaning $f$ followed by $g$. For sets $X$, $Y$ and $Z$, the inverse associator $X \sqcup (Y \sqcup Z) \to (X \sqcup Y) \sqcup Z$ is

$$\bigl\langle \langle \pi_1,\ \pi_2 \,;\, \pi_1 \rangle,\ \pi_2 \,;\, \pi_2 \bigr\rangle,$$

so it relates $\mathrm{inl}(x)$ to $\mathrm{inl}(\mathrm{inl}(x))$, $\mathrm{inr}(\mathrm{inl}(y))$ to $\mathrm{inl}(\mathrm{inr}(y))$ and $\mathrm{inr}(\mathrm{inr}(z))$ to $\mathrm{inr}(z)$, and nothing else.
