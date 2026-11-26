# Critical threshold for entropy-maximizing reproductive endpoints

**Setting.** For an age-structured population with Euler–Lotka reproductive distribution $p_j$ on the reproductive interval $A, \dots, D$, with Euler–Lotka-normalised survivorship weights $\ell_j$ (so $p_j = \ell_j / S_D$, $S_D = \sum_{j=A}^{D} \ell_j$), let $M_D = \sum_{j=A}^{D} j\,\ell_j$ be the first temporal moment, $T_D = M_D/S_D$ the generation time and $H(D)$ the evolutionary entropy (Shannon entropy of $(p_j)$ divided by $T_D$). In the geometric (Type II) regime, the normalised weights decay with ratio $q = \rho/\lambda \in (0,1)$ from age $A$, and $H(x)$ denotes the entropy as a function of a continuous endpoint $x \ge 1$.

**Theorem.**
1. *(Entropy collapse.)* As $D \to \infty$, $T_D \to \infty$ iff $M_D \to \infty$, and either condition implies $H(D) \to 0$. Consequently, if $M_D \to \infty$ and at least two reproductive classes carry positive mass, $H$ attains a finite global maximum at some $D^* > A$.
2. *(Unimodality.)* In the geometric regime $H(x)$ has at most one critical point on $[1, \infty)$, and any critical point is a strict local maximum.
3. *(Sharp threshold.)* The equation $q^A = 1 - q$ (that is, $q^A + q - 1 = 0$) has a unique root $q_c(A) \in (0,1)$. If $q < q_c(A)$, $H$ is strictly increasing on $[1, \infty)$ and approaches the asymptotic value $H_\infty$; if $q > q_c(A)$, $H$ has a unique interior maximum, a finite entropy-maximizing reproductive endpoint.

## Depends on

- [Evolutionary entropy of a Leslie population and its scale invariance](evolutionary-entropy-of-a-leslie-population.md)

## Expansion

Extending the reproductive window adds entropy (more classes share reproduction) but also lengthens the generation time. When late classes still carry substantial weight ($q$ close to $1$) the generation time eventually grows faster than the entropy, producing an interior maximum; when the weights decay quickly the added classes contribute little to $T$ and $H$ increases monotonically to $H_\infty$. The boundary between the regimes is where the derivative of $H$ at infinity changes sign, which reduces to $q^A + q - 1 = 0$. Empirically, reproductive windows of iteroparous animals cluster near the predicted entropy-maximizing classes.

## Sources

- J. Buescu, S. Elaydi, H. Oliveira, "Evolutionary Entropy Shapes Reproductive Lifespan in Age-Structured Populations", arXiv:2606.22001 (2026), Theorem 4.1, Corollary 4.3, Theorems 4.10 and 4.14, <https://doi.org/10.48550/arXiv.2606.22001>.
