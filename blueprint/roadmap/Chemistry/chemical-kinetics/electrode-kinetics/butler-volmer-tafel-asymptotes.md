# Tafel asymptotes of the Butler–Volmer current

At large overpotential one Butler–Volmer branch dominates: $\eta-\frac{1}{\alpha_anf}\ln\frac{j}{j_0}\to0$ as $\eta\to+\infty$ and $\eta+\frac{1}{\alpha_cnf}\ln\frac{-j}{j_0}\to0$ as $\eta\to-\infty$; against $\ln(|j|/j_0)$ the Tafel lines have slopes $+1/(\alpha_anf)$ and $-1/(\alpha_cnf)$.

For the [Butler–Volmer current density](butler-volmer-equation.md) with $j_0,\alpha_a,\alpha_c>0$, $n\ge1$, $T>0$
(so $j>0$ for $\eta>0$ and $j<0$ for $\eta<0$):

$$\lim_{\eta\to+\infty}\Big(\eta-\frac{1}{\alpha_anf}\ln\frac{j(\eta)}{j_0}\Big)=0,\qquad
\lim_{\eta\to-\infty}\Big(\eta+\frac{1}{\alpha_cnf}\ln\frac{-j(\eta)}{j_0}\Big)=0 .$$

With $L=\ln(|j|/j_0)$ the dimensionless log current, these say that in the $(L,\eta)$ plane each branch approaches a
Tafel line: $\eta=L/(\alpha_anf)$, of slope $+1/(\alpha_anf)$, on the anodic branch and $\eta=-L/(\alpha_cnf)$, of slope
$-1/(\alpha_cnf)$, on the cathodic branch. Both lines, extrapolated to $\eta=0$, give $L=0$, i.e. $|j|=j_0$, whereas the
actual current there is $j(0)=0$: $j_0$ is the extrapolated intercept. For $\eta>0$ the deviation from the
anodic line is $\frac{1}{\alpha_anf}\big|\ln\big(1-e^{-(\alpha_a+\alpha_c)nf\eta}\big)\big|$, which decays exponentially.

## Context

Undergraduate electrochemistry. Tafel plots are the standard way to read transfer coefficients and exchange currents from polarization data; decimal-logarithm slopes are $\ln 10$ times these.

## Depends on

- [Butler–Volmer equation](butler-volmer-equation.md)

## Proof depends on

None.

## Expansion

For $\eta>0$, $j/j_0=e^{\alpha_anf\eta}(1-e^{-(\alpha_a+\alpha_c)nf\eta})$, so $L=\alpha_anf\eta+\ln(1-e^{-(\alpha_a+\alpha_c)nf\eta})$, and the correction tends to $0$; the cathodic branch is the mirror computation. The slopes are those of the limiting lines, so no derivative of an inverse function is needed (Lecture 13, Sec. 3B, Fig. 1; IUPAC Tafel slope).

## Sources

- M. Z. Bazant, *10.626 Electrochemical Energy Systems*, MIT OpenCourseWare, Spring 2014, lecture notes, Lecture 13: Butler-Volmer equation, Sec. 3B (Tafel response, slope and intercept, Fig. 1). [Lecture PDF](https://old.ocw.mit.edu/courses/chemical-engineering/10-626-electrochemical-energy-systems-spring-2014/lecture-notes/MIT10_626S14_S11lec13.pdf); [course](https://ocw.mit.edu/courses/10-626-electrochemical-energy-systems-spring-2014/)
- E. R. Cohen, T. Cvitaš, J. G. Frey, B. Holmström, K. Kuchitsu, R. Marquardt, I. Mills, F. Pavese, M. Quack, J. Stohner, H. L. Strauss, M. Takami and A. J. Thor, *Quantities, Units and Symbols in Physical Chemistry* (IUPAC Green Book), 3rd edition, RSC Publishing, 2007, Section 2.13, p. 72 (Tafel slope $b=(\partial E/\partial\ln|I_F|)_{c_i,T,p}$, note 26). [doi:10.1039/9781847557889](https://doi.org/10.1039/9781847557889); [IUPAC PDF](https://iupac.org/wp-content/uploads/2019/05/IUPAC-GB3-2012-2ndPrinting-PDFsearchable.pdf)
