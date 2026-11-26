# Coexisting phase-locked patterns and the cycle space of the incidence matrix

**Setting.** As in [positive coupling weights realizing a phase-locked pattern](positive-coupling-weights-realizing-a-prescribed-phase-locked-pattern.md): a Kuramoto network on an undirected graph with $n$ nodes, $|\mathcal E|$ edges and $c$ connected components, incidence matrix $B$, edge weights $\delta$, zero-mean natural frequencies $\tilde\omega$, and phase-locked equilibria described by edge phase differences $x$ through $B\,D(x)\,\delta = \tilde\omega$ with $D(x) = \mathrm{diag}(\sin x_e)$.

**Proposition (coexistence).** For fixed weights $\delta$ with no zero entry, the equilibria compatible with the network are exactly the $x$ with

$$D(x)\,\delta \in B^{\dagger}\tilde\omega + \ker(B), \quad\text{equivalently}\quad \sin(x) \in \mathrm{diag}(\delta)^{-1}\big(B^{\dagger}\tilde\omega + \ker(B)\big),$$

where $\ker(B)$ is the cycle space, spanned by the signed edge vectors of the undirected cycles, of dimension $|\mathcal E| - n + c$. Conversely, a collection of patterns $x^{(1)}, \dots, x^{(\ell)}$ with no phase difference in $\pi\mathbb Z$ is simultaneously realizable by one weight vector if and only if

$$\bigcap_{i=1}^{\ell}\Gamma_i \neq \emptyset, \qquad \Gamma_i = D(x^{(i)})^{-1}\big(B^{\dagger}\tilde\omega + \ker(B)\big),$$

and by a nonnegative weight vector if and only if this intersection meets $\mathbb R^{|\mathcal E|}_{\ge 0}$.

**Examples** ($\delta = \mathbf 1$, $\tilde\omega = 0$, so the condition is $\sin(x) \in \ker B$).
- Trees: $\ker B = 0$, so the equilibria are the $2^{n-1}$ patterns with every edge difference in $\{0, \pi\}$.
- Cycles of length $n \ge 3$ (consistently oriented): $\ker B = \mathrm{span}(\mathbf 1)$; besides the $2^{n-1}$ patterns with $x_{k,k+1} \in \{0,\pi\}$ for $k < n$, there are the $n-1$ splay states with all edge differences equal to $2\pi m/n$, $m = 1, \dots, n-1$. A homogeneous 4-cycle has the continuum $x(\gamma) = (\tfrac\pi2 - \gamma, \tfrac\pi2 + \gamma, \tfrac\pi2 - \gamma, \tfrac\pi2 + \gamma)$.

**Stability.** The Jacobian at a phase-locked state is $J = -B\,\mathrm{diag}(A_e\cos x_e)\,B^{\top}$. If all weights are positive and all $|x_e| < \pi/2$, $-J$ is a weighted Laplacian and the pattern is stable up to the rotational mode; if some cosine-scaled weights $A_e\cos x_e$ are negative and the resulting signed network is structurally balanced, the pattern is unstable; in particular, for a line (path) network with positive weights the pattern is unstable as soon as some $|x_e| > \pi/2$.

## Depends on

- [Positive coupling weights realizing a prescribed phase-locked pattern](positive-coupling-weights-realizing-a-prescribed-phase-locked-pattern.md)

## Expansion

The equilibrium equation determines $D(x)\delta$ up to $\ker B$: one solution is $B^{\dagger}\tilde\omega$ (it exists because $\tilde\omega \perp \mathbf 1$ lies in the range of $B$ for connected $G$), and all others differ by the kernel. Solving for $\delta$ instead of $\sin x$ gives the affine sets $\Gamma_i$, so common weights exist exactly when the affine sets intersect. For a tree there is no cycle, hence no kernel; for a cycle the kernel is the circulation $\mathbf 1$, which constant sine vectors satisfy. On a path with positive weights, the Laplacian-type Jacobian with one negative edge weight $A_e\cos x_e < 0$ has a positive eigenvalue because removing that edge splits the tree into two blocks and the corresponding test vector gives a positive quadratic form.

## Sources

- T. Menara, G. Baggio, D. Bassett, F. Pasqualetti, "Functional control of oscillator networks", Nature Communications (2022), Eqs. (7)–(10) and Results sections on compatible functional patterns and on stability of functional patterns, <https://doi.org/10.1038/s41467-022-31733-2>, PMCID PMC9372149.
