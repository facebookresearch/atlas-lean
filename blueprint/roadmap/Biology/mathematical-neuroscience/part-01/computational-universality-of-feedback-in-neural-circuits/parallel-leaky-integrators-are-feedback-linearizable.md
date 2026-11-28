# Parallel leaky integrators with distinct time constants are feedback linearizable

**Lie-bracket criterion.** For smooth vector fields write $[f, g] = Dg\, f - Df\, g$, $\mathrm{ad}_f g = [f, g]$, $\mathrm{ad}_f^{i+1} g = [f, \mathrm{ad}_f^i g]$, and $L_f\phi = \nabla\phi \cdot f$. The system $x' = f(x) + g(x)v$ on $\mathbb{R}^n$ is globally feedback linearizable iff there is a smooth $\phi : \mathbb{R}^n \to \mathbb{R}$ with nowhere-vanishing gradient such that

1. $g, \mathrm{ad}_f g, \dots, \mathrm{ad}_f^{n-1} g$ are linearly independent at every $x$;
2. $L_{\mathrm{ad}_f^j g}\, \phi = 0$ for $j = 0, \dots, n-2$ and all $x$;
3. $x \mapsto \big(\phi(x), L_f\phi(x), \dots, L_f^{n-1}\phi(x)\big)$ is a bijection of $\mathbb{R}^n$.

Locally, linear independence together with involutivity of the distribution spanned by $g, \dots, \mathrm{ad}_f^{n-2} g$ is equivalent to feedback linearizability near a point (Frobenius).

**Statement.** The rate-model circuit

$$x_i' = -\lambda_i x_i + b_i v, \qquad i = 1, \dots, n,$$

with $\lambda_i > 0$ pairwise distinct and all $b_i \ne 0$, is globally feedback linearizable. It is a fading-memory system (each unit is a leaky integrator), so by the universality theorem for feedback-linearizable circuits it can emulate any $n$-th order system $z^{(n)} = G(z, \dots, z^{(n-1)}) + u$ with a single memoryless feedback, which here can be taken linear in $x$ plus the emulated nonlinearity. Whether a general recurrent rate network $x' = -\Lambda x + \sigma(Ax) + b v$ is in this class depends on $A$ and $b$; the criterion has to be checked case by case.

## Expansion

Here $f(x) = -\Lambda x$ with $\Lambda = \mathrm{diag}(\lambda_1, \dots, \lambda_n)$ and $g = b$ is constant, so $\mathrm{ad}_f^i g = \Lambda^i b$ up to sign. The matrix $(b, \Lambda b, \dots, \Lambda^{n-1} b) = \mathrm{diag}(b)\, V$ with the Vandermonde matrix $V_{jk} = \lambda_j^{k}$ is invertible because the $\lambda_j$ are distinct and $b_j \ne 0$, giving condition 1 (and controllability). Choose $\phi(x) = a^\top x$ with $a \ne 0$ orthogonal to $b, \Lambda b, \dots, \Lambda^{n-2} b$; this is condition 2. The vector $c_j = a_j b_j$ spans the left kernel of the $n \times (n-1)$ Vandermonde matrix, whose entries $c_j \propto \prod_{k \ne j}(\lambda_j - \lambda_k)^{-1}$ are all nonzero, so every $a_j \ne 0$. The map in condition 3 is linear with rows $a^\top(-\Lambda)^k$, i.e. a Vandermonde matrix times $\mathrm{diag}(a)$, hence bijective. The source also works a three-dimensional nonlinear example with a sigmoidal term, where the bracket conditions hold or fail depending on the parameters.

## Depends on

- [Universality of feedback-linearizable circuits under memoryless feedback](universality-of-feedback-linearizable-circuits-under-memoryless-feedback.md)

## Sources

- W. Maass, P. Joshi, E. D. Sontag, "Computational aspects of feedback in neural circuits", PLoS Computational Biology 3 (2007), e165, Methods ("Lie brackets", "A characterization of $S_n$ via Lie brackets", Theorem 4, "Application to neural network equations"), <https://doi.org/10.1371/journal.pcbi.0020165> (PMC1779299).
- E. D. Sontag, *Mathematical Control Theory*, 2nd ed., Springer (1998), Proposition 5.3.9 and Theorem 15 (Chapter 5).
