# Phase-averaged chronotherapy inequality

**Setting.** Model healthy cell populations by the periodic age-structured renewal system

$$\partial_tn_i+\partial_xn_i+d_i(t,x)\,n_i=0,\qquad n_i(t,0)=\sum_j\int_0^\infty B_{j\to i}(t,x)\,n_j(t,x)\,dx,$$

with $T$-periodic (for example circadian) coefficients and dominant Floquet eigenvalue $\lambda_F$. A drug acts only on the death rates. A periodic delivery schedule started at phase $\varphi\in[0,T)$ produces the death rates $d_i(t+\varphi,x)$ and eigenvalue $\lambda(\varphi)$. Constant infusion of the same daily dose produces the time-averaged death rates $T^{-1}\int_0^Td_i(t,x)\,dt$ and eigenvalue $\lambda_u$. The birth and transition rates are unaffected by the drug.

**Proposition.**

$$\lambda_u\ \le\ \frac1T\int_0^T\lambda(\varphi)\,d\varphi .$$

Consequently there is always a delivery phase $\varphi$ with $\lambda(\varphi)\ge\lambda_u$. A periodic schedule can be chosen to be no more toxic to healthy tissue than constant infusion, measured by the growth rate of the healthy population. Also, if some phase gives $\lambda(\varphi)<\lambda_u$ (more toxic), then some other phase gives $\lambda(\varphi)>\lambda_u$ (less toxic).

## Expansion

Averaging the death rates over phase shifts is a convex combination of the shifted death-rate profiles, here taken with the same unshifted birth rates. By convexity of $\lambda_F$ in the death rates (extended from two-point combinations to integrals), $\lambda_u$ is at most the phase average of $\lambda(\varphi)$. The inequality says nothing about how large the favourable window is. Depending on the coefficients, a small gain can be available over most phases, or a large gain only in a narrow window. This is the mathematical support for timing treatment to circadian rhythms, assuming tumour cells are less sensitive to those rhythms than healthy cells.

## Depends on

- [Convexity of the Floquet eigenvalue in death and birth rates](convexity-of-the-floquet-eigenvalue-in-death-and-birth-rates.md)

## Sources

- Jean Clairambault, Stéphane Gaubert, Thomas Lepoutre, "Circadian rhythm and cell population growth", arXiv:1006.3459 (2010), Section 3 (subsection "An argument in favor of the indirect influence of the circadian control on tumour cells"), consequence of Theorem 1, <https://doi.org/10.48550/arXiv.1006.3459>.
