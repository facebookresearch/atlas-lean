# Trace, determinant and second-compound test for an endemic equilibrium

**Second additive compound.** For a real $3 \times 3$ matrix $M = (m_{ij})$,

$$M^{[2]} = \begin{pmatrix} m_{11} + m_{22} & m_{23} & -m_{13} \\ m_{32} & m_{11} + m_{33} & m_{12} \\ -m_{31} & m_{21} & m_{22} + m_{33} \end{pmatrix};$$

its eigenvalues are the pairwise sums $\lambda_i + \lambda_j$ ($i < j$) of the eigenvalues of $M$.

**Lemma.** If $\operatorname{tr} M < 0$, $\det M < 0$ and $\det M^{[2]} < 0$, then all eigenvalues of $M$ have negative real part (and conversely).

**Application (SEIQR model with non-monotone incidence).** In a model with susceptible $S$, exposed $E$, infectious $I$, quarantined $Q$ and recovered $R$, recruitment $b$, natural death $\mu$, incidence $\beta S I (1 - \delta I)$, progression rate $\lambda$, recovery $\gamma$, disease death $\epsilon$, quarantine rates $d_3, d_2, d_1$ from $S, E, I$, release $\tau$ from quarantine and vaccination-type transfer $\eta$ from $S$ to $R$, the basic reproduction number is

$$\mathcal R_0 = \frac{\lambda \beta b}{(\eta + \mu + d_3)(\lambda + \mu + d_2)(\mu + \epsilon + \gamma + d_1)},$$

the disease-free equilibrium is locally asymptotically stable for $\mathcal R_0 < 1$, and for $\mathcal R_0 > 1$ a unique endemic equilibrium exists. Since $Q$ and $R$ do not feed back into $(S, E, I)$, the Jacobian at the endemic equilibrium has eigenvalues $-\mu$ and $-(\mu + \tau)$ plus those of the $3 \times 3$ block for $(S, E, I)$, to which the lemma applies, giving local asymptotic stability of the endemic equilibrium when $\mathcal R_0 > 1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [$R_0$ as a threshold for the linearized infected subsystem](../../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)

## Proof depends on

- [Routh–Hurwitz criterion for cubic polynomials](../../../../Analysis/control-theory/feedback-stability-and-classical-design/routh-hurwitz-criterion-for-cubic-polynomials.md)

## Expansion

For a $3 \times 3$ matrix with eigenvalues $\lambda_1, \lambda_2, \lambda_3$, $\det M = \lambda_1 \lambda_2 \lambda_3$, $\operatorname{tr} M = \sum \lambda_i$ and $\det M^{[2]} = \prod_{i<j} (\lambda_i + \lambda_j)$. If all three eigenvalues are real, $\det M < 0$ forces an odd number of negative ones; with $\operatorname{tr} M < 0$ and $\det M^{[2]} < 0$ the case of one negative and two positive eigenvalues is excluded. If $\lambda_{2,3} = \alpha \pm i\omega$, then $\det M^{[2]} = 2\alpha\,|\lambda_1 + \lambda_2|^2$, so $\det M^{[2]} < 0$ gives $\alpha < 0$ and $\det M < 0$ then gives $\lambda_1 < 0$. In the geometric approach (Li–Muldowney) the same compound matrix, evaluated along trajectories, yields Bendixson-type criteria that exclude periodic orbits and give global stability of the endemic equilibrium. The next-generation computation uses new infections $\beta S^0 I$ entering $E$ and transitions $E \to I$ at rate $\lambda$, with $S^0 = b/(\eta + \mu + d_3)$.

## Sources

- A. Khan, R. Zarin, G. Hussain, N. A. Ahmad, M. H. Mohd, A. Yusuf, "Stability analysis and optimal control of covid-19 with convex incidence rate in Khyber Pakhtunkhawa (Pakistan)", Results in Physics (2021), Section 2.1 (disease-free equilibrium and $\mathcal R_0$ by the next-generation method), Section 2.2 (endemic equilibrium), Theorem 1, Lemma 1 and Theorem 2 (local stability via trace, determinant and second compound). <https://doi.org/10.1016/j.rinp.2020.103703> (PMC7834202).
