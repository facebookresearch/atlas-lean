# No Hopf bifurcations in dual phosphorylation networks with three intermediates

**Setting.** In the full distributive and sequential dual-site phosphorylation network, a kinase $K$ phosphorylates $S_0\to S_1\to S_2$ and a phosphatase $F$ dephosphorylates $S_2\to S_1\to S_0$, each step proceeding through an enzyme–substrate intermediate ($KS_0, KS_1, FS_2, FS_1$) via a motif $E+S\rightleftharpoons ES\to E+S'$. Removing some intermediates gives mixed mechanisms in which a step occurs directly ($E+S\to E+S'$). Up to the symmetry exchanging kinase and phosphatase, the networks with exactly three intermediates are

$$\mathcal{G}_1:\quad S_0+K\rightleftharpoons KS_0\to S_1+K\rightleftharpoons KS_1\to S_2+K, \qquad S_2+F\rightleftharpoons FS_2\to S_1+F\to S_0+F,$$

$$\mathcal{G}_2:\quad S_0+K\rightleftharpoons KS_0\to S_1+K\rightleftharpoons KS_1\to S_2+K, \qquad S_2+F\to S_1+F\rightleftharpoons FS_1\to S_0+F,$$

with mass-action kinetics.

**Theorem.** Neither $\mathcal{G}_1$ nor $\mathcal{G}_2$, nor any network obtained from them by making some or all reversible reactions irreversible, admits a Hopf bifurcation, for any choice of positive rate constants and total amounts.

**Reduction lemma (Theorem 3.4 and its corollary).** Let $G$ be a mass-action network satisfying

- (A1) $G$ contains a motif $X_1+X_2\rightleftharpoons X_3\to c+\delta X_2$ with $X_1,X_2,X_3$ distinct species, $\delta\in\{0,1\}$ and $c$ a complex;
- (A2) $X_3$ appears in no other reaction;
- (A3) $c$ does not involve $X_1$, $X_2$ or $X_3$;
- (A4) $X_1$ is not a reactant of any reaction outside the motif;
- (A5) if other reactions involve $X_2$: (a) when $\delta=1$, any reaction outside the motif with $X_2$ in its product has $X_2$ as a catalyst and does not have $X_1$ in its product; (b) when $\delta=0$, reactions outside the motif have $X_2$ only in their products.

Let $G'$ be $G$ with the reverse reaction $X_3\to X_1+X_2$ removed. Then every reduced characteristic polynomial of the Jacobian of $G$ in convex parameters $(h,\ell)$ is also one of $G'$; hence if no reduced characteristic polynomial of $G'$ has a pair of purely imaginary roots, neither $G$ nor $G'$ admits a Hopf bifurcation.

## Expansion

In convex parameters the Jacobian is a polynomial in steady-state coordinates $h$ and extreme-ray coefficients $\ell$, and a simple Hopf bifurcation requires $\det H_1,\dots,\det H_{s-2}>0$, $\det H_{s-1}=0$ and $a_s>0$ for the Hurwitz matrices of the reduced characteristic polynomial. The reduction shows that reverse reactions of the form $X_3\to X_1+X_2$ in such motifs do not create imaginary roots, so it suffices to treat irreversible versions; for $\mathcal{G}_1$ and $\mathcal{G}_2$ every coefficient of $\det H_4$ as a polynomial in $\ell$ is positive whenever $a_5>0$, ruling out the Hopf condition. By contrast, the mixed mechanism with only two intermediates is known to oscillate.

## Sources

- E. Feliu, N. Kaihnsa, "Network reduction and absence of Hopf bifurcations in dual phosphorylation networks with three intermediates", *Studies in Applied Mathematics* 157(3) (2026), e70268, Theorem 3.4, Corollary 3.5 and Theorem 4.1, <https://doi.org/10.1111/sapm.70268> (preprint arXiv:2405.16179).
