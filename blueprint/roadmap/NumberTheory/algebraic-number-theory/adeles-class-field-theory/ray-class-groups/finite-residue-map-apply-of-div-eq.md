# Computing the finite residue map from a representation

Let $K$ be a number field and
$\mathfrak m$ a modulus of $K$ with finite part $\mathfrak m_0$. Let $x$ be a ray element of
$\mathfrak m$, and let $a, b \in \mathcal O_K$ have residue classes $\bar a, \bar b$ that are
units of $\mathcal O_K / \mathfrak m_0$ and satisfy $a / b = x$ in $K$. Then the finite residue
map of $\mathfrak m$ sends $x$ to $\bar a \bar b^{-1}$ in $(\mathcal O_K / \mathfrak m_0)^\times$.

Source (N406 §21.3): the representation-independence computation
[`coprime_rep_well_def`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L1757-L1810)
for the finite component.
