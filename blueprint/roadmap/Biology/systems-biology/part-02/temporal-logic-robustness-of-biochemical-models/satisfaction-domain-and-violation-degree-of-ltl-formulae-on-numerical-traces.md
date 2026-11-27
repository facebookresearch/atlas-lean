# Satisfaction domain and violation degree of LTL formulae on numerical traces

**Finite-trace LTL.** Let $T = (s_0, s_1, \dots, s_n)$ be a finite numerical trace (time, concentrations and derivatives at each sampled time), and let atomic propositions $\pi$ be real linear constraints on these quantities. LTL formulae are built from atoms with $\neg, \wedge, \vee, \to$ and the temporal operators $X$ (next), $F$ (eventually), $G$ (globally) and $U$ (until). With $T \models \phi$ iff $s_0 \models \phi$:

- $s_i \models X\phi$ iff ($i < n$ and $s_{i+1} \models \phi$) or ($i = n$ and $s_n \models \phi$);
- $s_i \models F\phi$ iff $\exists j \in [i, n]$ with $s_j \models \phi$; $\ s_i \models G\phi$ iff $\forall j \in [i, n]$, $s_j \models \phi$;
- $s_i \models \phi\, U \psi$ iff $\exists j \in [i, n]$ with $s_j \models \psi$ and $s_k \models \phi$ for all $k \in [i, j-1]$.

This is the standard semantics on the trace completed by a self-loop on its last state, so $\neg X\phi \equiv X\neg\phi$.

**Variable abstraction and satisfaction domain.** Replacing $q$ numerical constants of an LTL formula $\phi$ by real variables $y \in \mathbb{R}^q$ gives a quantifier-free formula $\phi(y)$ (QFLTL), and $\phi = \phi(y^\phi)$ for the vector $y^\phi$ of original constants. The satisfaction domain is $\mathcal D_{T, \phi(y)} = \{ y \in \mathbb{R}^q : T \models \phi(y)\}$.

**Proposition (computation of satisfaction domains).** $\mathcal D_{T,\phi(y)} = \mathcal D_{s_0, \phi(y)}$ with

$$\mathcal D_{s_i, \phi \wedge \psi} = \mathcal D_{s_i,\phi} \cap \mathcal D_{s_i,\psi}, \quad \mathcal D_{s_i, \phi \vee \psi} = \mathcal D_{s_i,\phi} \cup \mathcal D_{s_i,\psi}, \quad \mathcal D_{s_i, F\phi} = \bigcup_{j=i}^n \mathcal D_{s_j,\phi}, \quad \mathcal D_{s_i, G\phi} = \bigcap_{j=i}^n \mathcal D_{s_j,\phi},$$

$$\mathcal D_{s_i, \phi U \psi} = \bigcup_{j=i}^n \Big( \mathcal D_{s_j,\psi} \cap \bigcap_{k=i}^{j-1} \mathcal D_{s_k,\phi} \Big),$$

and $\mathcal D_{s_i, \pi(y)}$ the set of $y$ satisfying the linear constraint $\pi(y)$ at $s_i$. Hence $\mathcal D_{T,\phi(y)}$ is a finite union of convex polyhedra, computable with polyhedral libraries in time exponential in $q$ in the worst case but independent of the number of state variables.

**Violation and satisfaction degree.** For a distance on $\mathbb{R}^q$ (Euclidean by default),

$$vd(T, \phi) = \min_{y \in \mathcal D_{T,\phi(y)}} \| y - y^\phi \|, \qquad sd(T, \phi) = \frac{1}{1 + vd(T, \phi)} \in (0, 1].$$

$vd$ measures how much the constants of $\phi$ must change for it to hold on $T$; $sd = 1$ when $\phi$ holds (with a closed domain) and $sd \to 0$ as the trace moves far from satisfying it.

## Expansion

The proposition is a direct induction on the formula and the trace, mirroring the Boolean semantics with intersections for conjunction and universal quantification over time and unions for disjunction and existential quantification. Example: for $\phi(y_1, y_2) = F([A] > y_1 \wedge F [A] < y_2)$ ("$[A]$ rises above $y_1$ and later falls below $y_2$") on a trace whose maximum $10$ precedes its later minimum $2$, the domain is $\{y_1 \le 10,\ y_2 \ge 2\}$ (up to boundary conventions), so $vd(T, \phi(7,3)) = 0$, $vd(T, \phi(12,3)) = 2$ and $vd(T, \phi(14,3)) = 4$. Measuring distance in the low-dimensional formula space rather than between traces keeps the computation cheap, and the continuous degree is what makes averaging over perturbations meaningful.

## Sources

- A. Rizk, G. Batt, F. Fages, S. Soliman, "A general computational method for robustness analysis with applications to synthetic gene networks", Bioinformatics 25 (2009), i169–i178, Section 2.1 (finite-trace LTL semantics), Section 2.2 (Eq. (1), Proposition 1) and Section 2.3 (violation degree, Eq. (2)), <https://doi.org/10.1093/bioinformatics/btp200> (PMC2687954).
