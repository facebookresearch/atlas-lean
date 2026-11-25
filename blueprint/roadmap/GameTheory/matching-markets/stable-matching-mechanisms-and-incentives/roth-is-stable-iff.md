# Roth's market has exactly the two stable matchings $x$ and $y$

In Roth's market (men $m_1 : w_2 \succ w_1 \succ w_3$, $m_2, m_3 : w_1 \succ w_2 \succ w_3$; women
$w_1 : m_1 \succ m_3 \succ m_2$, $w_2 : m_3 \succ m_1 \succ m_2$, $w_3 : m_1 \succ m_2 \succ m_3$), a perfect
matching is stable if and only if it is $x = \{(m_1, w_2), (m_2, w_3), (m_3, w_1)\}$ or
$y = \{(m_1, w_1), (m_2, w_3), (m_3, w_2)\}$. The men prefer $x$ and the women prefer $y$, with $m_2$ and
$w_3$ indifferent. The proof checks all six perfect matchings.

## Background

- [Lattice of stable matchings](../lattice-of-stable-matchings/README.md): $x$ is the men's join of $x$ and $y$.

## Sources

- A. E. Roth, "The economics of matching: stability and incentives", *Mathematics of Operations Research* 7(4) (1982), 617–628, proof of Theorem 3 (the set `C(P)`).
