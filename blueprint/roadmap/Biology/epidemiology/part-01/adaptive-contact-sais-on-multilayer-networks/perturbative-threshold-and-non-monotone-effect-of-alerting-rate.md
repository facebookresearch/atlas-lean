# Perturbative threshold and the non-monotone effect of the alerting rate in adaptive-contact SAIS

**Setting.** Take the adaptive-contact SAIS model and its mean-field threshold $\tau_c(\bar\kappa)$, defined by the [nonlinear Perron–Frobenius problem](mean-field-threshold-as-a-nonlinear-perron-frobenius-eigenvalue.md) $z = \tau_c(\bar\kappa+1)F(z)$, on an M-connected two-layer network with default-contact matrix $W_S$ and alert-contact matrix $W_A$, where $\bar\kappa = \kappa/\beta$ is the relative alerting rate. For a nonnegative matrix $A$ with simple dominant eigenvalue $\lambda_1(A)$, right and left dominant eigenvectors $v = v_A$, $u = u_A$ normalized by $v^{\mathsf T}u = 1$, and a nonnegative matrix $B$ with $(Bv)_i > 0$ for all $i$, define

$$\Psi(A, B) = \sum_{i=1}^N u_i v_i\,\frac{\sum_j a_{ij} v_j}{\sum_j b_{ij} v_j}.$$

**Theorem (first-order expansions).**

$$\tau_c(\bar\kappa) = \frac{1}{\lambda_1(W_S)}\Big(1 + \bar\kappa\big(\Psi(W_S, W_A) - 1\big)\Big) + o(\bar\kappa) \quad (\bar\kappa \to 0),$$

$$\tau_c(\bar\kappa) = \frac{1}{\lambda_1(W_A)}\Big(1 + \bar\kappa^{-1}\big(\Psi(W_A, W_S) - 1\big)\Big) + o(\bar\kappa^{-1}) \quad (\bar\kappa \to \infty).$$

**Corollary (three regimes).** Assume $\lambda_1(W_S) > \lambda_1(W_A)$, so instantaneous adaptation raises the threshold from $1/\lambda_1(W_S)$ to $1/\lambda_1(W_A)$.

- If $\Psi(W_S, W_A) < 1$, then $\tau_c(\bar\kappa) < \tau_c(0)$ for small $\bar\kappa > 0$: slow contact adaptation *lowers* the epidemic threshold below that of no adaptation (undershooting).
- If $\Psi(W_A, W_S) > 1$, then $\tau_c(\bar\kappa) > \tau_c(\infty)$ for large $\bar\kappa$: a moderate alerting rate protects better than instantaneous adaptation (overshooting).
- If $\Psi(W_S, W_A) > 1$ and $\Psi(W_A, W_S) < 1$, both ends move toward the higher threshold; this holds in particular for pure contact reduction, $w^A_{ij} \le w^S_{ij}$ for all $i, j$ (the monotone case in the source).

**Lemma (symmetric layers cannot undershoot).** If $W_S$ and $W_A$ are both symmetric, then

$$\Psi(W_S, W_A) \ge \frac{\lambda_1(W_S)}{\lambda_1(W_A)},$$

so under $\lambda_1(W_S) > \lambda_1(W_A)$ the undershooting regime is impossible; asymmetry of contacts is needed for it.

## Depends on

- [Mean-field threshold of adaptive-contact SAIS as a nonlinear Perron–Frobenius eigenvalue](mean-field-threshold-as-a-nonlinear-perron-frobenius-eigenvalue.md)

## Expansion

At $\bar\kappa = 0$ the map is $F(z) = W_S z$ with solution $z = v_S$ and $\tau_c = 1/\lambda_1(W_S)$; as $\bar\kappa \to \infty$, $\bar\kappa F(z) \to W_A z$ and the solution tends to $v_A$ with $\tau_c \to 1/\lambda_1(W_A)$. Expanding $F$ to first order in $\bar\kappa$ (respectively $\bar\kappa^{-1}$) around these points and projecting onto the left eigenvector $u$, as in standard eigenvalue perturbation, gives the two expansions; the ratio of the two layers' neighborhood sums evaluated on the dominant eigenvector is what produces $\Psi$. The regimes read off the sign of the first-order coefficient: near $0$ it is the initial slope of $\tau_c$, and near $\infty$ it says whether $\tau_c$ approaches its limit from above, in which case, by continuity and $\tau_c(0) < \tau_c(\infty)$, the maximum is attained at a finite alerting rate. For contact reduction, $\sum_j w^S_{ij}v_j \ge \sum_j w^A_{ij}v_j$ for any positive $v$, giving $\Psi(W_S,W_A) > 1$ and $\Psi(W_A,W_S) < 1$. In the source's numerical study on a 115-node network with alert layers of spectral radius $\tfrac23\lambda_1(W_S)$, all three regimes appear.

## Sources

- F. D. Sahneh, A. Vajdi, J. Melander and C. M. Scoglio, "Contact adaption during epidemics: a multilayer network formulation approach", *IEEE Transactions on Network Science and Engineering* (2019), Section 5.2, Theorem 7, Eqs. (11)–(14), Lemma 6, and Section 6. <https://doi.org/10.1109/tnse.2017.2770091> (PMC7309295)
