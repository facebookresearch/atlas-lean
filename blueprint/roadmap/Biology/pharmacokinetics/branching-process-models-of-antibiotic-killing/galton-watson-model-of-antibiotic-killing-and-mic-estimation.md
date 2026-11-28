# Galton–Watson model of antibiotic killing and estimation of the minimal inhibitory concentration

**Model.** Bacteria exposed to an antibiotic at concentration $c \ge 0$ form a Galton–Watson process: in each generation every live cell independently dies, survives undivided or divides, with probabilities $p_0(c)$, $p_1(c)$, $p_2(c)$; the offspring mean is $m(c) = p_1(c) + 2p_2(c)$. Because qPCR measures the genomes of live and dead cells alike, one follows the two-type process $(X_n, Y_n)$ of live and dead cells and observes the total $Z_n = X_n + Y_n$. Starting from one cell, its mean $\mu_n = \mathbb{E}Z_n$ is

$$\mu_n = \frac{p_2 m^n - p_0}{m - 1} \ \ (m \neq 1), \qquad \mu_n = 1 + p_0 n \ \ (m = 1),$$

with $m^n \le \mu_n \le \frac{m(m^n - 1)}{2(m-1)} + 1$ when $m > 1$ and $1 \le \mu_n \le \frac{m(1 - m^n)}{2(1-m)} + 1$ when $m < 1$. The concentration–response is modelled as

$$m(c) = \frac{2}{1 + \alpha c^\beta}, \qquad \alpha, \beta > 0,$$

and the **minimal inhibitory concentration** is $\vartheta = \mathrm{MIC} = \min\{c : m(c) \le 1\} = \alpha^{-1/\beta}$.

**Data and estimators.** For each concentration $c_i$, $i = 1,\dots,K$, $N$ replicate cultures start from $x_0$ cells and are measured by qPCR after $n$ generations; the cycle-threshold readings are $C_j = a - \log_2 Z_n^{(j)} + \varepsilon_j$ with i.i.d. centred measurement errors of variance $\sigma_\varepsilon^2$ and a known constant $a$. Set $\log_2\widehat\mu_n = a - \log_2 x_0 - \frac1N\sum_{j=1}^N C_j$, let $\widehat m$ solve $\mu_n(\widehat m) = \widehat\mu_n$, obtain $(\widehat\alpha, \widehat\beta)$ from the least-squares regression of $\log(2/\widehat m(c_i) - 1)$ on $\log c_i$, and set $\widehat\vartheta = \widehat\alpha^{-1/\widehat\beta}$.

**Proposition.** As $x_0 \to \infty$ and $N \to \infty$:
1. $\widehat\mu_n$ is weakly consistent and $\frac{\sqrt N}{\sigma_\varepsilon}\big(\log_2\widehat\mu_n - \log_2\mu_n\big) \to N(0,1)$, so $\frac{\sqrt N\,(\widehat\mu_n - \mu_n)}{\sigma_\varepsilon\,\mu_n\log 2} \to N(0,1)$;
2. if $p_1 = 0$, $\widehat m$ is weakly consistent and $\frac{\mu_n'(m)}{\sigma_\varepsilon\,\mu_n(m)\log 2}\sqrt N(\widehat m - m) \to N(0,1)$;
3. $\widehat\alpha$, $\widehat\beta$ and $\widehat\vartheta$ are weakly consistent. With $\ell_i = \log c_i$, $L_1 = \sum_{i=1}^K\ell_i$, $L_2 = \sum_{i=1}^K\ell_i^2$ and

$$k_i = -\frac{2}{m(c_i)\big(2 - m(c_i)\big)}\,\frac{\sigma_\varepsilon\,\mu_n(m(c_i))\log 2}{\mu_n'(m(c_i))},$$

$\sqrt N(\widehat\alpha - \alpha, \widehat\beta - \beta)$ converges to a centred bivariate normal vector with covariance matrix $\begin{pmatrix}\sigma_\alpha^2 & \sigma_{\alpha\beta}\\ \sigma_{\alpha\beta} & \sigma_\beta^2\end{pmatrix}$, where

$$\sigma_\alpha^2 = \frac{\alpha^2}{(KL_2 - L_1^2)^2}\sum_{i=1}^K k_i^2(L_2 - L_1\ell_i)^2,\qquad \sigma_{\alpha\beta} = \frac{\alpha}{(KL_2 - L_1^2)^2}\sum_{i=1}^K k_i^2(K\ell_i - L_1)(L_2 - L_1\ell_i),\qquad \sigma_\beta^2 = \frac{1}{(KL_2 - L_1^2)^2}\sum_{i=1}^K k_i^2(K\ell_i - L_1)^2,$$

and $\sqrt N(\widehat\vartheta - \vartheta) \to N(0, \sigma_\vartheta^2)$ with

$$\sigma_\vartheta^2 = \frac{\vartheta^2(\log\alpha)^2}{\beta^2(KL_2 - L_1^2)^2}\sum_{i=1}^K k_i^2\Big(\frac{L_2 - L_1\ell_i}{\log\alpha} - \frac{K\ell_i - L_1}{\beta}\Big)^2 .$$

## Proof sketch

With many initial cells, $\log_2 Z_n^{(j)} = \log_2(x_0\mu_n) + O_P(x_0^{-1/2})$ by the central limit theorem for the branching process, so as $x_0 \to \infty$ the remaining randomness is the qPCR measurement error; part 1 is then the central limit theorem for the replicate mean, and part 2 is the delta method through the strictly increasing map $m \mapsto \mu_n(m)$. The Hill-type response linearises as $\log(2/m - 1) = \log\alpha + \beta\log c$, so ordinary least squares on the estimated $m(c_i)$ gives $(\widehat\alpha, \widehat\beta)$ and the MIC solves $m(c) = 1$. The method was applied to *Chlamydia trachomatis* treated with azithromycin and ciprofloxacin.

## Sources

- Anita Bogdanov, Péter Kevei, Máté Szalai and Dezső Virok, "Stochastic Modeling of In Vitro Bactericidal Potency", *Bulletin of Mathematical Biology* 84 (2022), 6, <https://doi.org/10.1007/s11538-021-00967-4>. Preprint version: arXiv:2104.11525 (2021), Sections 2–4, Lemma 1 and Propositions 1–3, <https://doi.org/10.48550/arXiv.2104.11525>.
