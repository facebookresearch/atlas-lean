# Positive PI control of the mean protein number

**Model.** In the two-stage gene expression network $\varnothing \xrightarrow{k_r} \text{mRNA}$, $\text{mRNA} \xrightarrow{\gamma_r} \varnothing$, $\text{mRNA} \xrightarrow{k_p} \text{mRNA} + \text{protein}$, $\text{protein} \xrightarrow{\gamma_p} \varnothing$ (all rates positive), the propensities are affine, so the first two moments of the chemical master equation close exactly. With $x_1, x_2$ the mean mRNA and protein numbers and $x_3, x_4, x_5$ the entries of the covariance matrix, $\dot x_1 = k_r - \gamma_r x_1$, $\dot x_2 = k_p x_1 - \gamma_p x_2$, and the covariance equations are linear in $(x_1,\dots,x_5)$ with input $k_r$. The system is asymptotically stable (Property 1) with equilibrium (Property 2)

$$x_1^* = \frac{k_r}{\gamma_r},\quad x_2^* = \frac{k_pk_r}{\gamma_p\gamma_r},\quad x_3^* = \frac{k_r}{\gamma_r},\quad x_4^* = \frac{k_pk_r}{\gamma_r(\gamma_p + \gamma_r)},\quad x_5^* = \frac{k_pk_r(\gamma_p + k_p + \gamma_r)}{\gamma_p\gamma_r(\gamma_p + \gamma_r)} .$$

Actuate the transcription rate (e.g. by light-induced transcription) with the positive PI law

$$k_r(t) = u(t) = \varphi\Big(k_1(\mu_* - x_2(t)) + k_2\int_0^t(\mu_* - x_2(s))\,ds\Big), \qquad \varphi(v) = \max\{0, v\},$$

for a reference mean protein number $\mu_* \ge 0$. The closed loop has the equilibrium $x_2^* = \mu_*$, $x_1^* = \mu_*\gamma_p/k_p$, $u^* = \mu_*\gamma_p\gamma_r/k_p$, integral state $I^* = u^*/k_2$ (Property 3): zero steady-state error.

**Lemma 4 (local, nominal).** For known $k_p, \gamma_p, \gamma_r > 0$, the equilibrium is locally exponentially stable if and only if

$$k_2 > 0 \quad\text{and}\quad k_1 > \frac{k_2}{\gamma_p + \gamma_r} - \frac{\gamma_p\gamma_r}{k_p} .$$

**Lemma 5 (local, robust).** If $(k_p, \gamma_p, \gamma_r) \in (0, k_p^+] \times [\gamma_p^-, \infty) \times [\gamma_r^-, \infty)$, the equilibrium is locally exponentially stable for all such parameters if and only if $k_2 > 0$ and $k_1 > k_2/(\gamma_p^- + \gamma_r^-) - \gamma_r^-\gamma_p^-/k_p^+$.

**Theorem 6 (global).** For $k_p, \gamma_p, \gamma_r > 0$ the equilibrium is globally asymptotically stable if $k_2 > 0$ and $k_1 > k_2/\gamma_p$.

The gain condition of Theorem 6 involves only the protein degradation rate, so a single controller tunes robustly across uncertain transcription and translation parameters; acting on $k_r$ alone, however, fixes the variance at $x_5^*$ once the mean is set.

## Depends on

- [Exponential perfect adaptation of the integral-feedback loop](../../integral-feedback-and-perfect-adaptation/exponential-perfect-adaptation-of-the-integral-feedback-loop.md)

## Proof depends on

- [Routh–Hurwitz criterion for cubic polynomials](../../../../Analysis/control-theory/feedback-stability-and-classical-design/routh-hurwitz-criterion-for-cubic-polynomials.md)

## Expansion

Near the equilibrium $u^* > 0$, so $\varphi$ is inactive and the augmented linear system in $(x_1, x_2, I)$ has state matrix $\begin{pmatrix}-\gamma_r & -k_1 & k_2\\ k_p & -\gamma_p & 0\\ 0 & -1 & 0\end{pmatrix}$; the Routh–Hurwitz criterion on its characteristic polynomial gives Lemma 4, and since the lower bound on $k_1$ is increasing in $k_p$ and decreasing in $\gamma_p, \gamma_r$, its worst case over the parameter box gives Lemma 5. Globally, $\varphi$ is a sector-$[0,1]$ nonlinearity around a marginally stable (integrating) loop, and an extension of the Popov criterion for marginally stable systems reduces stability to positivity of a quadratic polynomial in $\omega^2$; Descartes' rule of signs shows positivity when $k_1 > k_2/\gamma_p$ for a suitable multiplier, and $u^* > 0$ keeps the equilibrium off the dead zone of $\varphi$.

## Sources

- Corentin Briat and Mustafa Khammash, "Computer control of gene expression: Robust setpoint tracking of protein mean and variance using integral feedback", 2012 IEEE 51st IEEE Conference on Decision and Control (CDC) (2012), 3582–3588, <https://doi.org/10.1109/cdc.2012.6426720>; numbering as in arXiv:1207.4766: Properties 1–3, Lemmas 4 and 5, Theorem 6 and Proposition 10.
