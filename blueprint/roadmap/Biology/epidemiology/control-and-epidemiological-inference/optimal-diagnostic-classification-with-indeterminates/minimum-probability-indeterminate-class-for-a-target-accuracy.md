# Minimum-probability indeterminate class for a target accuracy

**Setting.** Measurements $r \in \Omega$ have density $P(r)$ for positive and $N(r)$ for negative samples, both summable and assigning zero mass to single points; with prevalence $p$, a test sample has density $Q(r) = pP(r) + (1-p)N(r)$. A classification partitions $\Omega$ (up to null sets) into positive, negative and indeterminate domains $D_P, D_N, D_h$. The error rate $E[D_P,D_N] = \int_{D_P}(1-p)N + \int_{D_N}pP$ does not count indeterminates; the accuracy restricted to classified samples is $L = 1 - E/\int_{D}Q$, $D = D_P \cup D_N$.

**Binary optimum.** With no indeterminate class, the error is minimized by

$$D_P^\star = \{r : pP(r) > (1-p)N(r)\}, \qquad D_N^\star = \{r : (1-p)N(r) > pP(r)\},$$

with the tie set $\{pP = (1-p)N\}$ split arbitrarily when it has positive measure. Define the local accuracy of this rule,

$$Z^\star(r) = \frac{\max\{pP(r),\ (1-p)N(r)\}}{Q(r)} \in [\tfrac12, 1].$$

**Theorem.** Let $X$ be a target accuracy with $L[D_P^\star, D_N^\star] < X$, and suppose $Z^\star > X$ on a set of positive measure. Among all classifications whose classified samples have accuracy exactly $X$,

$$p\int_{D_P}P + (1-p)\int_{D_N}N = X\int_D Q,$$

the probability $\int_{D_h}Q$ of the indeterminate class is minimized by

$$D_h = \{r : Z^\star(r) < Z_0(X)\} \cup C(X), \qquad D_P = D_P^\star \setminus D_h, \qquad D_N = D_N^\star \setminus D_h,$$

where the threshold $Z_0 = Z_0(X)$ and the set $C(X)$ below are any choice for which the classified region $D = \Omega\setminus(\{Z^\star < Z_0\}\cup C)$ has positive probability, $\int_D Q > 0$, and

$$\int_{\Omega\setminus(\{Z^\star < Z_0\}\cup C)} \big(Z^\star(r) - X\big)\,Q(r)\,dr = 0$$

with $C(X) \subset \{Z^\star = Z_0\}$ (empty when the level set is $Q$-null). The positivity requirement matters: an empty classified region also makes the displayed integral vanish, but there the accuracy of classified samples is undefined and everything is held out. Thus the samples to hold out are those with the lowest local accuracy: $Z_0(X)$ is an upper bound on the local accuracy of held-out samples and a lower bound on that of classified samples ($Z^\star \le Z_0$ on $D_h$ and $Z^\star \ge Z_0$ on $D$, up to null sets). Neither bound need be attained, and $Z_0(X)$ need not be unique: if $Z^\star$ takes no values in an interval up to a $Q$-null set, every cutoff in that gap gives the same sets. For example, on three intervals of equal $Q$-mass where $Z^\star$ equals $0.5$, $0.8$ and $1$ and $X = 0.9$, the optimum holds out the first interval, the largest held-out local accuracy is $0.5$, the smallest classified one is $0.8$, and every $Z_0 \in (0.5, 0.8]$ solves the threshold equation with $C = \emptyset$ and a nonempty classified region. The choice $Z_0 = 1$, $C = \{Z^\star = 1\}$ (or any $Z_0 > 1$) also makes the integral zero, but classifies nothing and holds out mass $1$ rather than the attainable $1/3$; it is excluded by $\int_D Q > 0$.

## Expansion

The function $I(\zeta) = \big(\int_{D(\zeta)}Q\big)^{-1}\int_{D(\zeta)}(Z^\star - X)Q$, with $D(\zeta) = \{Z^\star \ge \zeta\}$, is nondecreasing in $\zeta$ (constant across gaps in the values of $Z^\star$), is negative at $\zeta = 1/2$ and positive for some larger $\zeta$, so it changes sign at some $Z_0(X)$ at which $D(Z_0)$ still has positive probability, unique only when $I$ is strictly increasing there; at a jump, part of the level set $\{Z^\star = Z_0\}$ is added via $C$, using continuity of the integral in the measure of $C$. Optimality is an exchange argument: any point with $Z^\star < Z_0$ is farther below $X$ than any point with $Z^\star > Z_0$, so moving a classified point into the holdout and a held-out point back costs more indeterminate mass to keep the constraint. Because $1/2 \le Z^\star \le 1$, a solution $Z_0(X)$ can be found by bisection starting at $3/4$.

## Sources

- P. N. Patrone, P. Bedekar, N. Pisanic, Y. C. Manabe, D. L. Thomas, C. D. Heaney, A. J. Kearsley, "Optimal decision theory for diagnostic testing: minimizing indeterminate classes with applications to saliva-based SARS-CoV-2 antibody assays", Mathematical Biosciences (2022), Eqs. (3)–(14) and Lemma 1 with its proof, <https://doi.org/10.1016/j.mbs.2022.108858>, PMCID PMC9195412.
