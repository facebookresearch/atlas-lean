# Finite residue map

Let $K$ be a number field and $\mathfrak m$ a modulus of $K$ with finite
part $\mathfrak m_0$, a nonzero ideal of $\mathcal O_K$. The finite residue map of $\mathfrak m$ is
the group homomorphism from the ray elements of $\mathfrak m$ to
$(\mathcal O_K / \mathfrak m_0)^\times$ sending $x$ to $\bar a \bar b^{-1}$, where $x = a / b$ with
$a, b \in \mathcal O_K$ whose residue classes $\bar a, \bar b$ are units of
$\mathcal O_K / \mathfrak m_0$; such $a$ and $b$ exist, and the value does not depend on their
choice.

Source (N406 §21.3): the
[`finitePartMapHom`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L1812-L1864)
finite component of the quotient isomorphism.
