# Zimm–Bragg partition function and its long-chain limit

The Zimm–Bragg partition function has the closed form $q(n)=\big(\lambda_+^{n+1}(1-\lambda_-)-\lambda_-^{n+1}(1-\lambda_+)\big)/(\lambda_+-\lambda_-)$ in the transfer-matrix eigenvalues; for fixed $\sigma>0$ and long chains the helicity tends to $s\,\partial\ln\lambda_+/\partial s$, which equals $1/2$ at $s=1$ with slope $1/(4\sqrt\sigma)$ there.

**Setting.** The [Zimm–Bragg model](zimm-bragg-helix-coil-model.md) with $s,\sigma>0$ and transfer matrix $M=\begin{pmatrix}1&\sigma s\\1&s\end{pmatrix}$.

**Statement.**

1. The eigenvalues of $M$ are real and distinct,

$$\lambda_\pm=\frac{(1+s)\pm\sqrt{(1-s)^2+4\sigma s}}{2},$$

and for every $n\ge1$

$$q(n)=\frac{\lambda_+^{\,n+1}(1-\lambda_-)-\lambda_-^{\,n+1}(1-\lambda_+)}{\lambda_+-\lambda_-}.$$

2. For fixed $\sigma>0$, as $n\to\infty$, $\frac1n\ln q(n)\to\ln\lambda_+$ and the fractional helicity $\theta_H(n;s)$ converges to

$$\theta_\infty(s)=s\,\frac{\partial\ln\lambda_+}{\partial s}=\frac12\left(1+\frac{s-1}{\sqrt{(s-1)^2+4\sigma s}}\right).$$

3. $\theta_\infty(1)=1/2$ and $\theta_\infty'(1)=1/(4\sqrt\sigma)$. For finite $n$ the helicity at $s=1$ is in general not $1/2$ (for $n=1$, $\theta_H=\sigma/(1+\sigma)$, about $0.002$ for $\sigma=0.002$).
4. If $s$ follows a van 't Hoff law $d\ln s/dT=\Delta h_{HC}/(k_BT^2)$ (molecular enthalpy per segment; equivalently $\Delta H_{HC}/(RT^2)$ with a molar enthalpy) with $s(T_m)=1$ at some $T_m>0$, and $\sigma>0$ is constant, then the long-chain melting curve satisfies

$$\left|\frac{d\theta_\infty}{dT}\right|_{T=T_m}=\frac{|\Delta h_{HC}|}{4\sqrt{\sigma}\,k_BT_m^2},$$

which is the source's melting-curve slope at $T_m$, written in magnitude.

## Context

Graduate biophysics. These formulas quantify cooperativity in helix–coil and DNA melting transitions; Tokmakoff tabulates measured $\sigma\approx2$–$3\times10^{-3}$ and helix propagation enthalpies near $-1$ kcal per mole of residues for model polypeptides (empirical values).

## Depends on

- [Zimm–Bragg model of the helix–coil transition](zimm-bragg-helix-coil-model.md)

## Proof depends on

None.

## Expansion

Proof of item 1: the characteristic polynomial $\chi(\lambda)=\lambda^2-(1+s)\lambda+s(1-\sigma)$ has positive discriminant $(1-s)^2+4\sigma s$ and $\chi(1)=-\sigma s<0$, so $\lambda_-<1<\lambda_+$; and $\lambda_++\lambda_-=1+s>0$ gives $|\lambda_-|<\lambda_+$, which is all the limit needs ($\lambda_-$ can be below $-1$ when $\sigma$ is large, for example $s=1$, $\sigma=5$). Diagonalize $M$ and evaluate $(1\;0)M^n(1\;1)^{\mathsf T}$; at $n=1$ the formula gives $q(1)=1+\sigma s$ using $\lambda_+\lambda_-=s(1-\sigma)$.

Proof route for item 2 (the step that must be written out): write $q=A\lambda_+^{\,n}\big(1+(B/A)\rho^n\big)$ with $A=\lambda_+(1-\lambda_-)/(\lambda_+-\lambda_-)>0$, $B=-\lambda_-(1-\lambda_+)/(\lambda_+-\lambda_-)$ and $\rho=\lambda_-/\lambda_+$, $|\rho|<1$. Then $\frac{s}{n}\partial_s\ln q=s\,\partial_s\ln\lambda_++\frac sn\partial_s\ln A+\frac sn\partial_s\ln(1+(B/A)\rho^n)$. On a compact $s$-interval in $(0,\infty)$, with $\sigma$ fixed, choose $r<1$ above the supremum of $|\rho|$ on the interval; the derivatives of $A,B,\rho$ and $|B/A|$ are bounded there, so for large $n$ the denominator $1+(B/A)\rho^n$ is at least $1/2$, and the last two terms are $O(1/n)$ and $O(n r^{n-1}/n)$ uniformly. Convergence of $\frac1n\ln q$ alone would not justify differentiating the limit; this decomposition gives the pointwise convergence of item 2 (a uniform version is not claimed). Item 3 is direct evaluation of the closed form of $\theta_\infty$; this form is algebraically equal to Tokmakoff's long-chain expression (checked numerically at several $(s,\sigma)$). Item 4 is the chain rule $d\theta_\infty/dT=\theta_\infty'(1)\,s\,d\ln s/dT$ at $T_m$.

**Correction to the source.** Tokmakoff prints $\lambda_\pm=\frac12((1-s)\pm\tilde\lambda)$ with $\tilde\lambda=((1-s)^2+4\sigma s)^{-1/2}$; the trace of $M$ is $1+s$ and the eigenvalue gap is $((1-s)^2+4\sigma s)^{+1/2}$, as his long-chain formulas require. The statement uses the corrected values, and the closed form and limits were checked numerically against brute-force enumeration for small $n$ and by finite differences.

Remaining decomposition before the page can be marked ready: the convergence argument above written as a lemma, and the elementary bounds on $A$, $B$, $\rho$ and their $s$-derivatives on compact intervals.

## Sources

- A. Tokmakoff, *Concepts in Biophysical Chemistry*, LibreTexts, Section 18.1 "Helix–Coil Transition" (read at [chem.libretexts.org](https://chem.libretexts.org/Bookshelves/Biological_Chemistry/Concepts_in_Biophysical_Chemistry_%28Tokmakoff%29/05:_Cooperativity/18:_Cooperativity/18.01:_HelixCoil_Transition)), subsections "Multiple stretches" (closed form of $q_{\mathrm{conf}}$, long-chain limit, $\theta_H$, $(d\theta/ds)_{s=1}=1/(4\sigma^{1/2})$, finite-chain discussion), "Temperature Dependence" (melting-curve slope at $T_m$) and the table of calorimetric parameters.
