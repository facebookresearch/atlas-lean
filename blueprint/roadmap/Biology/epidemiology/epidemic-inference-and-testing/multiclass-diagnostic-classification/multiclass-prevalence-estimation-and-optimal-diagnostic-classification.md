# Multiclass prevalence estimation and optimal diagnostic classification

**Setting.** A diagnostic assay returns a measurement $\mathbf r$ in a measurement space $\Omega\subseteq\mathbb R^d$. The tested population consists of $n\ge2$ classes $C_1,\dots,C_n$ (for an antibody test: naive, previously infected, vaccinated, ...) with unknown **generalized prevalences** $q_1,\dots,q_n\ge0$, $\sum_kq_k=1$, and known class-conditional densities $P_1,\dots,P_n$ (bounded and integrable, with single points of measure zero). The measurement density of a random sample is the mixture $Q(\mathbf r)=\sum_kq_kP_k(\mathbf r)$.

**Prevalence estimation.** Fix any partition $\{D_j\}_{j=1}^n$ of $\Omega$ into nonempty measurable sets (not necessarily classification domains) and let $P_{j,k}=\int_{D_j}P_k$ and $Q_j=\int_{D_j}Q=\sum_kP_{j,k}q_k$. Eliminating $q_n=1-\sum_{k<n}q_k$ gives

$$\mathbf q=(\mathbf P-\mathbf P_n)^{-1}\bigl(\overline{\mathbf Q}-\overline{\mathbf P_n}\bigr),$$

where $\mathbf q=(q_1,\dots,q_{n-1})$, $\mathbf P=(P_{i,j})_{i,j<n}$, $\mathbf P_n$ is the $(n-1)\times(n-1)$ matrix with entries $P_{i,n}$, $\overline{\mathbf Q}=(Q_j)_{j<n}$ and $\overline{\mathbf P_n}=(P_{j,n})_{j<n}$, assuming $\mathbf P-\mathbf P_n$ is invertible. Replacing $Q_j$ by the empirical fraction $\hat Q_j=S^{-1}\sum_{i=1}^S\mathbf 1\{\mathbf r_i\in D_j\}$ of $S$ samples gives estimates $\hat q_k$ that are unbiased, $\mathbb E[\hat q_k]=q_k$, and converge in mean square as $S\to\infty$. No classification of individual samples is needed.

**Optimal classification (Lemma, Appendix A).** Among partitions $\{D_j\}$ of $\Omega$ (each measurement assigned to exactly one class up to null sets), the prevalence-weighted total misclassification

$$\mathscr L(D_1,\dots,D_n)=\sum_{j=1}^nq_j\int_{\Omega\setminus D_j}P_j(\mathbf r)\,d\mathbf r$$

is minimized by

$$D_j^\star=\{\mathbf r:q_jP_j(\mathbf r)>q_kP_k(\mathbf r)\ \text{for all }k\ne j\},$$

provided the tie sets $\mathscr E_j=\bigcup_{k\ne j}\{q_kP_k=q_jP_j=\max_iq_iP_i\}$ have measure zero; otherwise ties may be assigned arbitrarily (for instance to the lowest-indexed tied class) without changing the loss.

## Expansion

$\mathscr L=1-\sum_jq_j\int_{D_j}P_j$, so minimizing it means maximizing $\int\sum_j\mathbf 1_{D_j}(\mathbf r)\,q_jP_j(\mathbf r)\,d\mathbf r$, which is achieved pointwise by assigning each $\mathbf r$ to a class with maximal $q_jP_j(\mathbf r)$; this is the Bayes classifier with prior $q$, and it shows that the same measurement can be classified differently as prevalence changes. Prevalence estimation inverts the linear map from class proportions to bin probabilities; any partition works, but the conditioning of $\mathbf P-\mathbf P_n$ (how well the bins separate the classes) controls the variance, so a natural choice is a preliminary classification partition. For $n=2$ the formula reduces to the classical Rogan-Gladen correction of an apparent prevalence by sensitivity and specificity.

## Sources

- R. A. Luke, A. J. Kearsley, P. N. Patrone, "Optimal classification and generalized prevalence estimates for diagnostic settings with more than two classes", *Mathematical Biosciences* 358 (2023), 108982, Section 3 (Eqs. for prevalence estimation and optimal domains) and the Lemma of Appendix A, <https://doi.org/10.1016/j.mbs.2023.108982> (preprint arXiv:2210.02366).
