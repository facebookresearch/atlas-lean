# The map $\psi_{SBT}$

Encode a Stern–Brocot vertex by its gap $(a, b)$ of fractions: its
label is the mediant $a \oplus b$ (numerators added, denominators added), and its left and right
children are the vertices with gaps $(a, a \oplus b)$ and $(a \oplus b, b)$. Let $v_L$ and $v_R$
be the left and right children of a vertex $v$. If the label of $v_L$ has odd numerator, then
$\psi_{SBT}(v)$ is the list consisting of $v_L$ followed by the left and right children of
$v_R$; otherwise it is the list consisting of the left and right children of $v_L$ followed by
$v_R$.

## Sources

- Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25 (2025), Article A78, Section 2.3 (definition of `ψ_SBT`).
