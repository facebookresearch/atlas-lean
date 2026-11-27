# Functional lower bound method for linear IPS

If every polynomial that agrees with $1/f$ on the Boolean cube is hard for a circuit class $\mathcal{C}$, then the system $f, \vec{x}^2 - \vec{x}$ has no $\mathcal{C}$-$\mathrm{IPS}_{\mathrm{LIN}}$ refutation; for multilinear classes this even rules out $\mathcal{C}$-IPS refutations, turning functional circuit lower bounds into proof lower bounds.

Let $f \in \mathbb{F}[x_1, \dots, x_n]$ be such that the system $f(\vec{x}), x_1^2 - x_1, \dots, x_n^2 - x_n$ is unsatisfiable, so $f(\vec{x}) \ne 0$ for every $\vec{x} \in \{0,1\}^n$.

1. Let $\mathcal{C} \subseteq \mathbb{F}[\vec{x}]$ be closed under partial evaluation. If every $g \in \mathbb{F}[\vec{x}]$ with $g(\vec{x}) = 1/f(\vec{x})$ for all $\vec{x} \in \{0,1\}^n$ satisfies $g \notin \mathcal{C}$, then $f, \vec{x}^2 - \vec{x}$ has no $\mathcal{C}$-$\mathrm{IPS}_{\mathrm{LIN}}$ refutation.
2. Let $\mathcal{C}$ be closed under evaluation and let $\mathcal{D} = \{p - q : p, q \in \mathcal{C}\}$. If every such $g$ satisfies $g \notin \mathcal{D}$, then $f, \vec{x}^2 - \vec{x}$ has no $\mathcal{C}$-$\mathrm{IPS}_{\mathrm{LIN}'}$ refutation. If moreover $\mathcal{C}$ consists of multilinear polynomials, then $f, \vec{x}^2 - \vec{x}$ has no $\mathcal{C}$-IPS refutation.

**Degree instance.** Let $n \ge 1$, $\mathrm{char}(\mathbb{F}) > n$ and $\beta \in \mathbb{F} \setminus \{0, \dots, n\}$. If $g \in \mathbb{F}[\vec{x}]$ satisfies $g(\vec{x}) (\sum_i x_i - \beta) = 1 \bmod \vec{x}^2 - \vec{x}$, then $\deg g \ge n$; the earlier bound of Impagliazzo, Pudlák and Sgall was $\lceil n/2 \rceil + 1$, and the tight value $n$ is what the lifted lower bounds need.

## Proof sketch

For part 1, a refutation $C = g(\vec{x}) y + \sum_i h_i(\vec{x}) z_i$ gives $g = C(\vec{x}, 1, \vec{0}) \in \mathcal{C}$ and $g f \equiv 1$ modulo the Boolean axioms, so $g = 1/f$ on the cube, a contradiction. For part 2 write $C = C_1(\vec{x}, \vec{z}) y + C_0(\vec{x}, \vec{z})$; the refutation conditions force $C_0(\vec{x}, \vec{0}) = 0$ and $C_1(\vec{x}, \vec{0}) f \equiv 1$, while $C_1(\vec{x}, \vec{0}) = C(\vec{x}, 1, \vec{0}) - C(\vec{x}, 0, \vec{0}) \in \mathcal{D}$; a multilinear $C$ has degree at most one in $y$ automatically. The method needs only one non-Boolean axiom, so as stated it does not encode systems arising from 3CNFs.

## Depends on

- [Linear and circuit-restricted Ideal Proof Systems](linear-and-restricted-ideal-proof-systems.md)

## Proof depends on

None.

## Sources

- Michael A. Forbes, Amir Shpilka, Iddo Tzameret, Avi Wigderson, "Proof complexity lower bounds from algebraic circuit complexity", *31st Computational Complexity Conference (CCC 2016)*, LIPIcs 50, 2016, https://doi.org/10.4230/LIPIcs.CCC.2016.32; numbering of arXiv:1606.05050v1 (Lemmas 5.1 and 5.2, Corollary 5.4).
- Tuomas Hakoniemi, Nutan Limaye, Iddo Tzameret, "Functional lower bounds in algebraic proofs: symmetry, lifting, and barriers", *56th ACM Symposium on Theory of Computing (STOC 2024)*, 2024, https://doi.org/10.1145/3618260.3649616; numbering of arXiv:2412.20114v1 (Theorem 1, restating the method).
