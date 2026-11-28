# Crosstalk-induced bifurcation in the two-input Oja rule

**Setting.** A neuron with two input channels learns weights $\mathbf w = (w_1, w_2)$ by the averaged Oja rule with synaptic crosstalk (inspecific Hebbian updates):

$$\dot{\mathbf w} = \mathbf{EC}\,\mathbf w - (\mathbf w^{T}\mathbf C\,\mathbf w)\,\mathbf w,$$

where the input covariance and the error (crosstalk) matrix are

$$\mathbf C = \begin{pmatrix} v + \delta & c \\ c & v \end{pmatrix}, \qquad \mathbf E = \begin{pmatrix} q & 1-q \\ 1-q & q \end{pmatrix},$$

with update quality $q \in (1/2, 1]$ ($q = 1$ means no crosstalk), $v > 0$, negative input correlation $c < 0$, $v > |c|$, $v > |\delta|$ and $\det \mathbf C = v(v+\delta) - c^2 > 0$. The parameter $\delta$ measures input bias. Set $\beta = qc + (1-q)v$ and $q^* = v/(v - c) \in (1/2, 1)$.

**Spectrum.** $\mathbf{EC}$ has real eigenvalues

$$\mu_{1,2} = \tfrac12\Big(2(1-q)c + q(2v + \delta) \pm \sqrt{\Delta}\Big), \qquad \Delta = \big[2qc + (1-q)(2v+\delta)\big]^2 + (2q-1)\delta^2,$$

with eigenline slopes $z_{1,2} = (-q\delta \pm \sqrt\Delta)/(2\beta)$; they coincide exactly when $\delta = 0$ and $q = q^*$. The eigenlines are invariant under the flow.

**Equilibria (distinct eigenvalues).** The equilibria are the origin, which repels, and the two opposite pairs of eigenvectors of $\mathbf{EC}$ normalised by $\mathbf w^T\mathbf C\mathbf w = \mu$. The pair for the larger eigenvalue $\mu_1$ are hyperbolic attracting nodes; the pair for $\mu_2$ are saddles. The phase plane has no cycles, and the two attractors have open half-planes as basins.

**Unbiased inputs ($\delta = 0$): bifurcation at $q^*$.**

- If $q > q^*$ (little crosstalk), $\mu_1 = (2q-1)(v-c)$ with direction $w_2 = -w_1$: the attractors $\pm\sqrt{2q - 1}\,(1,-1)/\sqrt2$, of norm $\sqrt{2q - 1}$, are segregated (one input wins); the saddles lie on $w_2 = w_1$ with norm $1$.
- If $q < q^*$ (strong crosstalk), $\mu_1 = v + c$ with direction $w_2 = w_1$: the attractors $\pm(1,1)/\sqrt2$ have norm $1$ and are unsegregated; the saddles lie on $w_2 = -w_1$ with norm $\sqrt{2q - 1}$.
- If $q = q^*$, every line through the origin is invariant and carries two half-stable equilibria, which together form an ellipse of non-isolated equilibria.

So with unbiased, negatively correlated inputs, crosstalk above the critical level $1 - q^*$ abolishes ocular-dominance-like segregation through an exchange of stability between the two eigendirections. For $\delta \ne 0$ the eigenvalues never cross and no bifurcation occurs.

## Proof sketch

At an equilibrium $\mathbf{EC}\mathbf w = (\mathbf w^T\mathbf C\mathbf w)\mathbf w$, so $\mathbf w$ is an eigenvector of $\mathbf{EC}$ scaled so that $\mathbf w^T\mathbf C\mathbf w$ equals its eigenvalue. The eigenvalues are the roots of $X^2 - \operatorname{tr}(\mathbf{EC})X + \det(\mathbf{EC})$ with $\det(\mathbf{EC}) = (2q-1)\det\mathbf C > 0$, and the discriminant is a sum of squares, hence real. Linearisation at a normalised eigenvector shows two negative eigenvalues for the top direction and opposite signs for the other. On the line $w_2 = -w_1$, $\mathbf w^T\mathbf C\mathbf w = (v - c)|\mathbf w|^2$ and the eigenvalue is $(2q-1)(v-c)$, so the normalised equilibria have $|\mathbf w|^2 = 2q - 1$ (norm $1$ at $q = 1$, plain Oja); on $w_2 = w_1$ both sides equal $v + c$ and the norm is $1$. For $\delta = 0$ the slope $z = w_2/w_1$ obeys $\dot z = -\beta(z^2 - 1)$, and $\beta$ changes sign exactly at $q = q^*$. This swaps which of $z = \pm1$ is attracting and makes $\dot z \equiv 0$ at criticality. A planar system whose invariant lines carry all the equilibria has no periodic orbits.

## Sources

- Anca Raˇdulescu and Paul Adams, "Hebbian crosstalk and input segregation", *Journal of Theoretical Biology* 337 (2013), 133–149, <https://doi.org/10.1016/j.jtbi.2013.08.004>. Preprint version: arXiv:1207.7257 (2012), Section 1.3, Lemmas 2.1 and 2.2, Section 2.1, Proposition 2.5 and Corollary 2.6, <https://doi.org/10.48550/arXiv.1207.7257>.
