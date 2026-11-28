# Inverse of the Butler–Volmer relation

For positive exchange current density and transfer coefficients, the Butler–Volmer current is a smooth strictly increasing bijection of $\mathbb R$ onto $\mathbb R$ with $j(0)=0$: each current density has exactly one activation overpotential, of the same sign. With equal coefficients the inverse is $\eta=\frac{1}{\alpha nf}\operatorname{arsinh}\frac{j}{2j_0}$.

Let $j(\eta)=j_0\big(e^{\alpha_anf\eta}-e^{-\alpha_cnf\eta}\big)$ be the [Butler–Volmer current density](butler-volmer-equation.md)
with $j_0>0$, $\alpha_a>0$, $\alpha_c>0$, $n\ge1$, $T>0$ and $f=F/(RT)$. Then $j:\mathbb R\to\mathbb R$ is infinitely
differentiable, strictly increasing and bijective, with $j(0)=0$, $j(\eta)\to+\infty$ as $\eta\to+\infty$ and
$j(\eta)\to-\infty$ as $\eta\to-\infty$. Hence each current density $\bar j\in\mathbb R$ is produced by exactly one
activation overpotential $\eta(\bar j)$, and $\eta(\bar j)$ has the sign of $\bar j$: it is positive, zero or negative
exactly when $\bar j$ is.

In the symmetric case $\alpha_a=\alpha_c=\alpha$,

$$j(\eta)=2j_0\sinh(\alpha nf\eta),$$

and the inverse is

$$\eta(\bar j)=\frac{1}{\alpha nf}\operatorname{arsinh}\!\Big(\frac{\bar j}{2j_0}\Big)=\frac{1}{\alpha nf}\ln\!\Big(\frac{\bar j}{2j_0}+\sqrt{1+\frac{\bar j^2}{4j_0^2}}\Big).$$

## Context

Undergraduate electrochemistry. Inverting Butler–Volmer is how battery and fuel-cell models turn an imposed current into an activation voltage loss; the symmetric case $\alpha=1/2$ is the common default. The slope of $j$ at $\eta=0$ is on the [linear-response page](butler-volmer-linear-response.md), and the behaviour at large overpotential on the [Tafel asymptotes page](butler-volmer-tafel-asymptotes.md).

## Depends on

- [Butler–Volmer equation](butler-volmer-equation.md)

## Proof depends on

- [Mean value theorem for real functions](../../../Analysis/real-functions/differential-calculus/mean-value-theorem.md)
- [Intermediate value theorem](../../../Analysis/real-functions/continuity-and-functional-equations/intermediate-value-theorem.md)

## Expansion

The general statement is derived from the constitutive law; the sources state the law and, for equal coefficients, the arsinh inverse.

1. $j'(\eta)=j_0nf\big(\alpha_ae^{\alpha_anf\eta}+\alpha_ce^{-\alpha_cnf\eta}\big)>0$ for every $\eta$, so by the mean value theorem $j(\eta_2)-j(\eta_1)=j'(\xi)(\eta_2-\eta_1)>0$ for $\eta_1<\eta_2$: $j$ is strictly increasing, hence injective. Clearly $j(0)=0$.
2. For $\eta\ge0$, $j(\eta)\ge j_0\big(e^{\alpha_anf\eta}-1\big)$, and for $\eta\le0$, $j(\eta)\le j_0\big(1-e^{-\alpha_cnf\eta}\big)$; since $e^{s}\to+\infty$ as $s\to+\infty$, $j\to\pm\infty$ as $\eta\to\pm\infty$.
3. Given $\bar j$, choose $a<b$ with $j(a)\le\bar j\le j(b)$ by step 2; $j$ is continuous on $[a,b]$, so the intermediate value theorem gives $\eta\in[a,b]$ with $j(\eta)=\bar j$. With step 1 this $\eta$ is unique, and comparing with $j(0)=0$ gives its sign.
4. With $\alpha_a=\alpha_c=\alpha$, $e^u-e^{-u}=2\sinh u$, and $\operatorname{arsinh}y=\ln(y+\sqrt{1+y^2})$ is the two-sided inverse of $\sinh$; composing with the positive scalings $\eta\mapsto\alpha nf\eta$ and $y\mapsto2j_0y$ gives the displayed inverse (Lecture 13, Sec. 3C).

Step 2 needs the limit $e^s\to+\infty$ as $s\to+\infty$ (in Mathlib `Real.tendsto_exp_atTop`), and step 4 needs the inverse pair $\sinh$, $\operatorname{arsinh}$ (in Mathlib `Real.sinh_bijective`, `Real.sinh_arsinh`, `Real.arsinh_sinh`). A good expansion adds pages for these two facts.

## Sources

- M. Z. Bazant, Theory of chemical kinetics and charge transfer based on nonequilibrium thermodynamics, *Accounts of Chemical Research* 46 (2013), 1144–1160; numbers from arXiv:1208.1587v5, section “Generalized Butler–Volmer kinetics”, Eq. (27) (the Butler–Volmer law with transfer coefficients $\alpha_a$, $\alpha_c$). [arXiv:1208.1587v5](https://arxiv.org/abs/1208.1587v5); [doi:10.1021/ar300145c](https://doi.org/10.1021/ar300145c)
- E. R. Cohen, T. Cvitaš, J. G. Frey, B. Holmström, K. Kuchitsu, R. Marquardt, I. Mills, F. Pavese, M. Quack, J. Stohner, H. L. Strauss, M. Takami and A. J. Thor, *Quantities, Units and Symbols in Physical Chemistry* (IUPAC Green Book), 3rd edition, RSC Publishing, 2007, Section 2.13, p. 72 (overpotential, exchange current density and transfer coefficients, notes 23–25). [doi:10.1039/9781847557889](https://doi.org/10.1039/9781847557889); [IUPAC PDF](https://iupac.org/wp-content/uploads/2019/05/IUPAC-GB3-2012-2ndPrinting-PDFsearchable.pdf)
- M. Z. Bazant, *10.626 Electrochemical Energy Systems*, MIT OpenCourseWare, Spring 2014, lecture notes, Lecture 13: Butler-Volmer equation, Sec. 3C (symmetric electron transfer: hyperbolic-sine form inverted by the inverse hyperbolic sine) and Fig. 2. [Lecture PDF](https://old.ocw.mit.edu/courses/chemical-engineering/10-626-electrochemical-energy-systems-spring-2014/lecture-notes/MIT10_626S14_S11lec13.pdf); [course](https://ocw.mit.edu/courses/10-626-electrochemical-energy-systems-spring-2014/)
- Original attribution: A. J. Bard and L. R. Faulkner, *Electrochemical Methods: Fundamentals and Applications*, 2nd edition, Wiley, 2001, for the Butler–Volmer equation. The opened sources above supply the constitutive law and the symmetric inverse used here.
