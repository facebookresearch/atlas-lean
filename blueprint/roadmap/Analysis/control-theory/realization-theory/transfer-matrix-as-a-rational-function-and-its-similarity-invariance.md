# The transfer matrix as a rational function, and its invariance under similarity

Let $\mathbb{K}$ be a field, $A \in \mathbb{K}^{n \times n}$, $B \in \mathbb{K}^{n \times m}$, $C \in \mathbb{K}^{p \times n}$ and $D \in \mathbb{K}^{p \times m}$. For $s \in \mathbb{K}$ with $\det(sI - A) \ne 0$ define the transfer matrix

$$G(s) = C (sI - A)^{-1} B + D \in \mathbb{K}^{p \times m}.$$

1. **Rational form.** In the field of rational functions $\mathbb{K}(X)$, let

    $$\mathcal{G} = \frac{C \operatorname{adj}(XI - A)\, B}{\det(XI - A)} + D \in \mathbb{K}(X)^{p \times m}.$$

    Every entry of $\mathcal{G}$ is a ratio of polynomials with denominator $\det(XI - A)$, the characteristic polynomial of $A$. At every $s$ with $\det(sI - A) \ne 0$, evaluating these entries at $s$ gives $G(s)$.

2. **Similarity invariance.** For invertible $T \in \mathbb{K}^{n \times n}$, the system $(TAT^{-1}, TB, CT^{-1}, D)$ has the same characteristic polynomial and the same rational transfer matrix $\mathcal{G}$. It therefore has the same transfer matrix $G(s)$ at every $s$ with $\det(sI - A) \ne 0$, and it realizes the same Markov sequence $(D, CB, CAB, CA^2B, \dots)$.

**Proof.**

- **Part 1.** The adjugate $\operatorname{adj}(M)$ has entries that are polynomials with integer coefficients in the entries of $M$, and $M \operatorname{adj}(M) = \det(M) I$. Evaluation at $s$ is a ring homomorphism $\mathbb{K}[X] \to \mathbb{K}$, so it sends $\operatorname{adj}(XI - A)$ to $\operatorname{adj}(sI - A)$ and $\det(XI - A)$ to $\det(sI - A)$. When $\det(sI - A) \ne 0$, the matrix $\operatorname{adj}(sI - A)/\det(sI - A)$ is $(sI - A)^{-1}$.
- **Part 2.** We have $XI - TAT^{-1} = T(XI - A)T^{-1}$, so the two determinants agree and $\operatorname{adj}(XI - TAT^{-1}) = T \operatorname{adj}(XI - A)\, T^{-1}$. Hence $CT^{-1} \operatorname{adj}(XI - TAT^{-1})\, TB = C \operatorname{adj}(XI - A)\, B$. The Markov parameters satisfy $CT^{-1}(TAT^{-1})^k TB = CA^kB$.

## Background

- [Minimal realizations are unique up to a unique similarity](minimal-realizations-are-similar.md): similar triples realize the same Markov sequence, and minimal realizations of one sequence are similar
- [Laplace transform of the matrix exponential and of the state of a linear system](laplace-transform-of-the-state-of-a-linear-system.md): the transfer matrix as the Laplace transform of the impulse response over $\mathbb{R}$ and $\mathbb{C}$

## Sources

- K. J. Åström and R. M. Murray, *Feedback Systems: An Introduction for Scientists and Engineers*, 2nd ed., Princeton University Press, 2021 (electronic edition v3.0i, <http://fbsbook.org>), Section 9.2, realizations $G(s) = C(sI - A)^{-1}B + D$ and their invariance under the coordinate change $z = Tx$ (pp. 9-12–9-13).
- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 6.5, Definition 6.5.8: similar triples realize the same Markov sequence (p. 286).
