# Geometric program characterization of the basic reproduction number

**Setting.** Linearize a compartmental epidemic model at a disease-free equilibrium that is stable in the absence of new infections. The infected states $x \in \mathbb{R}^n$ obey $\dot x = (F + V)x$, where $F \in \mathbb{R}_{\ge 0}^{n \times n}$ collects new infections and $V$ is Metzler (nonnegative off-diagonal entries) and Hurwitz (all eigenvalues with negative real part). The basic reproduction number is $R_0 = \rho(-F V^{-1})$. Write $V = V_{od} - V_d$ with $V_d \ge 0$ diagonal and $V_{od} \ge 0$ with zero diagonal.

**Theorem (characterizations of $R_0$).**

1. *Stability characterization:*

$$
R_0 = \inf_{r > 0}\{\, r : F + rV \text{ is Hurwitz} \,\}.
$$

2. *Geometric program characterization:*

$$
R_0 = \inf_{r > 0,\ w > 0}\Big\{\, r : \operatorname{diag}(r V_d w)^{-1}\,(F + r V_{od})\,w \le \mathbf{1}_n \,\Big\}.
$$

The constraint in (2) is a posynomial inequality in $(r, w)$ divided by a monomial, so (2) is a geometric program and becomes convex after the change of variables $r = e^{s}$, $w = e^{u}$.

**Optimal allocation.** Let a resource vector $\theta \ge 0$ act on the parameters so that $F(\theta)$, $V_{od}(\theta)$, the cost $c(\theta)$ and constraints $h(\theta) \le \mathbf{1}_q$ are entrywise posynomials, $V_d(\theta)$ is entrywise a monomial, the feasible set $\{\theta \ge 0 : h(\theta) \le \mathbf{1}_q\}$ is bounded, and $V_{od}(\theta) - V_d(\theta)$ is Hurwitz on it. Then the $R_0$-constrained problem $\min\{c(\theta) : h(\theta) \le \mathbf{1}_q,\ R_0(\theta) \le r_{\max}\}$ and the budget-constrained problem $\min\{R_0(\theta) : h(\theta) \le \mathbf{1}_q,\ c(\theta) \le c_{\max}\}$ are equivalent (the first as a limit of geometric programs with slack $\tau \to 0^+$) to geometric programs in $(r, w, \theta)$. If in addition $F(\theta)$ and $V_{od}(\theta)$ are nonincreasing and $V_d(\theta)$ is nondecreasing in $\theta$, then $R_0(\theta)$ is nonincreasing in $\theta$ on the feasible set.

## Depends on

- [$R_0$ as a threshold for the linearized infected subsystem](../../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)

## Expansion

For Metzler Hurwitz $H$ and nonnegative $E$, $H + E$ is Hurwitz if and only if $\rho(-EH^{-1}) < 1$. With $H = rV$ and $E = F$ this gives $F + rV$ Hurwitz iff $R_0 < r$, hence (1). For Metzler matrices, being Hurwitz is equivalent to the existence of $w > 0$ with $(F + rV)w < 0$; a relaxation lemma shows the strict inequality can be replaced by $\le$ without changing the infimum. Splitting $V$ into its diagonal and off-diagonal parts and dividing row by row by $r V_d w$ rewrites $(F + rV)w \le 0$ as the posynomial-over-monomial constraint in (2). Substituting this representation of $R_0(\theta)$ into the allocation problems yields geometric programs. In numerical vaccine and antidote examples, targeting $R_0$ gives qualitatively different allocations from targeting the spectral abscissa of $F + V$.

## Sources

- Kevin D. Smith, Francesco Bullo, "Convex Optimization of the Basic Reproduction Number", IEEE Transactions on Automatic Control (2022), 1–8, <https://doi.org/10.1109/tac.2022.3212012>. Published version of arXiv:2109.07643, cited next; locators there refer to the arXiv version.
- Kevin D. Smith, Francesco Bullo, *Convex Optimization of the Basic Reproduction Number*, arXiv 2021. Definition 1, Lemma 3, Theorem 1 (characterizations of $R_0$), Lemma 4 (monotonicity), Definition 2 and Theorem 2 (geometric program transcription), Lemma 5. <https://doi.org/10.48550/arXiv.2109.07643>
