# Lieb's concavity theorem

Fix a Hermitian $d \times d$ complex matrix $H$. The map $A \mapsto \operatorname{tr} \exp(H + \log A)$ is concave on the cone of positive definite $d \times d$ matrices, where $\log A$ is defined by the functional calculus.

## Idea

For numbers, $a \mapsto e^{h + \log a} = e^h a$ is linear, so concavity is a genuinely noncommutative phenomenon. Lieb proved it in 1973, together with the joint concavity of $(A, B) \mapsto \operatorname{tr}(K^* A^q K B^r)$ for $q, r \ge 0$ with $q + r \le 1$, which also carries his name and resolved the Wigner–Yanase–Dyson conjecture. The joint form implies the joint convexity of quantum relative entropy and the strong subadditivity of von Neumann entropy. The exponential form, with Jensen's inequality, gives $\mathbb{E}\operatorname{tr}\exp(H + X) \le \operatorname{tr}\exp(H + \log \mathbb{E}\,e^X)$, which makes matrix cumulant generating functions subadditive and drives the modern matrix concentration inequalities.

## Statements

- [Lieb's concavity theorem](lieb-concavity.md)
- [Lieb's concavity theorem, joint form](lieb-concavity-trace-rpow.md): the joint-concavity form, also called Lieb's concavity theorem
- [Lieb's concavity theorem, case $q = 0$](lieb-concavity-trace-rpow-of-left-eq-zer.md): its case $q = 0$
- [Lieb's concavity theorem, case $r = 0$](lieb-concavity-trace-rpow-of-right-eq-ze.md): its case $r = 0$
- [Concavity of $A \mapsto \operatorname{tr}(K^* A^q K)$](concave-on-re-trace-conj-rpow.md): concavity of $A \mapsto \operatorname{tr}(K^* A^q K)$, used for these cases

## Related topics

- [Matrix concentration inequalities](../../../Probability/concentration-inequalities/matrix-concentration-inequalities/README.md)
- [Peierls and Klein inequalities](../../../Analysis/operator-theory/eigenvalue-inequalities/peierls-and-klein-inequalities/README.md)
