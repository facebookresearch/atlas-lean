# Accessible paths to the fitness maximum on the unoriented hypercube

**Setting.** Let $Q_n$ be the unoriented binary hypercube $\{0,1\}^n$ (edges between vertices at Hamming distance $1$, so back mutations are allowed), with House-of-Cards fitnesses: independent $U(0,1)$ values, except that a target vertex $\mathbf v = \mathbf v_n$ is the a priori global maximum. For $x \in (0,1]$ let $\vartheta(x)$ be the unique nonnegative solution of

$$ (\sinh\vartheta)^x(\cosh\vartheta)^{1-x} = 1 . $$

Let $X$ be the number of accessible (fitness-increasing) paths from $\mathbf 0$ to $\mathbf v$, and $\mathbb P^\alpha$ the law conditional on $\omega(\mathbf 0) = \alpha$.

**Theorem.** Suppose $|\mathbf v_n|/n \to x \ge 0.002$, where $|\mathbf v|$ is the number of ones. Then

$$ \lim_{n\to\infty}\mathbb P^\alpha(X \ge 1) = \begin{cases} 0, & \alpha > 1 - \vartheta(x),\\ 1, & \alpha < 1 - \vartheta(x).\end{cases} $$

Equivalently, the reduced first-passage site percolation time with $U(0,1)$ costs satisfies $\mathcal T'_V(\mathbf 0, \mathbf v_n) \to \vartheta(x)$ in probability. Integrating over $\alpha$:

- for the antipodal target $\mathbf v = \mathbf 1$ ($x = 1$, $\vartheta = \operatorname{arsinh} 1 = \ln(1+\sqrt2)$),

$$ \mathbb P(X \ge 1) \to 1 - \ln\big(1 + \sqrt2\big); $$

- for a uniformly random location of the maximum ($x = \tfrac12$, $\sinh\vartheta\cosh\vartheta = 1$, so $\vartheta = \tfrac12\ln(2+\sqrt5)$),

$$ \mathbb P(X \ge 1) \to 1 - \tfrac12\ln\big(2 + \sqrt5\big). $$

This resolves the Berestycki–Brunet–Shi conjecture that the critical starting fitness is given by the first-moment threshold $1 - \vartheta(x)$, where $\big(\mathbb E^\alpha X\big)^{1/n} \to \sinh(1-\alpha)^x\cosh(1-\alpha)^{1-x}$.

## Depends on

- [Accessibility percolation equals first-passage site percolation](accessibility-percolation-equals-first-passage-site-percolation.md)

## Expansion

The first-moment bound gives the upper half of the threshold. For the lower half, the equivalence with first-passage site percolation reduces the claim to showing $\mathcal T'_V(\mathbf 0, \mathbf v_n) \le \vartheta(x) + \varepsilon$ with high probability. With exponential instead of uniform costs (asymptotically equivalent for small total costs), first-passage percolation on $Q_n$ is coupled to a *clustering translation process*, a branching-type particle system on the hypercube in which the birth time of the first surviving particle at a vertex is its passage time. A second-moment-type argument then compares $S$, the expected number of particles at $\mathbf v_n$ by time $\vartheta_n$ with vertex-minimal ancestral lines (shown to be $\Theta(1)$), with $B$, an expected count of "contested" particle pairs (shown to be $O(1)$ when $x$ exceeds a technical constant $x^* \approx 0.00167$), and a Poisson-type inequality bounds the probability of an uncontested particle at $\mathbf v_n$ from below by $S\exp(-B/S)$; the final step upgrades this bounded-below probability to $\mathbb P(\mathcal T'_V(\mathbf 0, \mathbf v_n) \le \vartheta(x) + \varepsilon) \to 1$ for every $\varepsilon > 0$. The specific values follow from $\int_0^1 \mathbf 1\{\alpha < 1 - \vartheta\}\,d\alpha = 1 - \vartheta$.

## Sources

- Anders Martinsson, "Accessibility percolation and first-passage site percolation on the unoriented binary hypercube", arXiv:1501.02206 (2015), Section 1 (Theorems 1.1–1.3 and 1.6), Section 3 (clustering translation process, Proposition 3.1, Theorem 3.6), Sections 4–5 (Propositions 4.2–4.7, Proposition 5.1). <https://doi.org/10.48550/arXiv.1501.02206>
