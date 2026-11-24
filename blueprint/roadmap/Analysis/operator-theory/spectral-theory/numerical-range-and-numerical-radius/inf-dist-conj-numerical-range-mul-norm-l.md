# Lower bound from the numerical range, conjugate form

Let $H$ be a complex inner
product space, whose inner product $\langle \cdot, \cdot \rangle$ is conjugate-linear in its
first argument and linear in its second, let $T : H \to H$ be a bounded linear operator and let
$W(T) = \{\langle T x, x \rangle : x \in H,\ \|x\| = 1\} \subseteq \mathbb{C}$ be its numerical
range. For $z \in \mathbb{C}$ let $d(\overline{z}, W(T))$ be the infimum of the distances from
the complex conjugate $\overline{z}$ to the points of $W(T)$, taken to be $0$ when $W(T)$ is
empty. Then for every $\psi \in H$, $d(\overline{z}, W(T))\,\|\psi\| \le \|(T - zI)\psi\|$,
where $I$ is the identity operator on $H$. The space $H$ need not be complete.

The conjugate appears because $\langle T x, x \rangle$ is the complex conjugate of
$\langle x, T x \rangle$: $W(T)$ is the complex conjugate of the set
$\{\langle x, T x \rangle : \|x\| = 1\}$ used in
`infDist_numericalRange_mul_norm_le_norm_sub_smul_apply`.
