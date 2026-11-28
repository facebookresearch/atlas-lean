# Barrier: functional lower bounds cannot handle Boolean instances

The functional lower bound method cannot prove any lower bound for a Boolean instance against a sufficiently strong proof system, one that can efficiently derive the arithmetized conjunction of its axioms.

**Instance admitting a functional lower bound.** Let $\mathcal{C} \subseteq \mathbb{F}[\vec{x}]$ be a circuit class closed under partial field-element assignments, and let $\mathcal{F} = \{f_i(\vec{x}) = 0\}_i$ be equations in $\mathcal{C}$ that are unsatisfiable together with $\vec{x}^2 - \vec{x}$. $\mathcal{F}$ admits a functional lower bound against $\mathcal{C}$-$\mathrm{IPS}_{\mathrm{LIN}'}$ if there is $f \in \mathcal{C}$ with $f, \vec{x}^2 - \vec{x}$ unsatisfiable such that (1) no $g \in \mathcal{C}$ satisfies $g = 1/f$ on $\{0,1\}^n$, and (2) there is a $\mathcal{C}$-$\mathrm{IPS}_{\mathrm{LIN}'}$ proof of $\mathcal{F}$ from $f = 0$ and the Boolean axioms. In that case $\mathcal{F}$ has no $\mathcal{C}$-$\mathrm{IPS}_{\mathrm{LIN}'}$ refutation.

**Sufficiently strong proof system.** A proof system $P$ for equations in $\mathcal{C}$ that is simulated by some $\mathcal{C}'$-$\mathrm{IPS}_{\mathrm{LIN}'}$ with $\mathcal{C}' \supseteq \mathcal{C}$ closed under partial assignments and polynomially many sums of products is sufficiently strong if, for some arithmetization scheme (a translation of Boolean formulas into polynomials preserving their values on the cube), every set of Boolean equations $\{f_i = 0\}_i$ has a $P$-derivation of the arithmetization of $\bigwedge_i f_i$ of size $\mathrm{poly}(\sum_i |f_i|)$.

**Theorem.** Let $P$ be a sufficiently strong proof system for equations in $\mathcal{C}$, simulated by $\mathcal{C}'$-$\mathrm{IPS}_{\mathrm{LIN}'}$ where $\mathcal{C}' \supseteq \mathcal{C}$ is closed under partial assignments and under polynomially many sums of products ($h_i, g_i \in \mathcal{C}'$ for $i \in I$ with $|I| = \mathrm{poly}(n)$ imply $\sum_{i \in I} h_i g_i \in \mathcal{C}'$). Let $\mathcal{F} = \{f_i(\vec{x}) = 0\}_i$ be equations in $\mathcal{C}$ with every $f_i$ Boolean (taking only values in $\{0,1\}$ on $\{0,1\}^n$) and with no common Boolean root, and let $f \in \mathcal{C}'$ have no Boolean root. If $\mathcal{F}$ has a $\mathcal{C}'$-$\mathrm{IPS}_{\mathrm{LIN}'}$ proof from $f = 0$ and $\vec{x}^2 - \vec{x}$, then some $g \in \mathcal{C}'$ satisfies $g(\vec{x}) = 1/f(\vec{x})$ for all $\vec{x} \in \{0,1\}^n$. Hence condition (1) fails for $f$ and $\mathcal{C}'$, and no Boolean instance admits a functional lower bound against $\mathcal{C}'$-$\mathrm{IPS}_{\mathrm{LIN}'}$ in the sense above.

*Remark (examples from the source):* Hakoniemi, Limaye and Tzameret note (Section 7, after Definition 64, and STOC Theorem 1.9) that $\mathrm{AC}^0[p]$-Frege, $\mathrm{TC}^0$-Frege and constant-depth $\mathrm{IPS}_{\mathrm{LIN}'}$ satisfy the conjunction-derivation condition, so the method gives no lower bounds against them for Boolean instances.

## Proof sketch

The proof of $\mathcal{F}$ from $f = 0$ gives $g_i \in \mathcal{C}'$ with $g_i f = f_i$ modulo the Boolean axioms. Because $P$ is sufficiently strong and simulated by $\mathcal{C}'$-$\mathrm{IPS}_{\mathrm{LIN}'}$, there are $h_i \in \mathcal{C}'$ with $\sum_i h_i f_i = 1 - \prod_i (1 - f_i)$, the arithmetization of $\bigwedge_i f_i$. Since the $f_i$ are Boolean with no common Boolean root, $\prod_i (1 - f_i)$ vanishes on the cube, so $\big(\sum_i h_i g_i\big) f \equiv 1$ modulo the Boolean axioms, and $g = \sum_i h_i g_i$ lies in $\mathcal{C}'$ by closure under sums of products. This complements the simulation of $\mathrm{AC}^0[p]$-Frege by constant-depth IPS over $\mathbb{F}_p$: functional lower bounds alone cannot resolve $\mathrm{AC}^0[p]$-Frege lower bounds through IPS. Previously known hard instances for fragments of IPS, such as subset sum, are all non-Boolean.

## Depends on

- [Functional lower bound method for linear IPS](functional-lower-bound-method.md)
- [Linear and circuit-restricted Ideal Proof Systems](linear-and-restricted-ideal-proof-systems.md)

## Proof depends on

None.

## Sources

- Tuomas Hakoniemi, Nutan Limaye, Iddo Tzameret, "Functional lower bounds in algebraic proofs: symmetry, lifting, and barriers", *56th ACM Symposium on Theory of Computing (STOC 2024)*, 2024, https://doi.org/10.1145/3618260.3649616; numbering of arXiv:2412.20114v1 (Definitions 62 and 64, Observation 63, Theorem 65, Section 7).
