# Exponential payoff-to-fitness Moran process: exact fixation probabilities

**Setting.** A well-mixed population of $n \ge 2$ individuals of types $A$ and $B$ plays a game with payoff matrix

$$\begin{pmatrix} a & b \\ c & d \end{pmatrix}$$

(row player's payoff; $A$ against $A$ gets $a$, $A$ against $B$ gets $b$, $B$ against $A$ gets $c$, $B$ against $B$ gets $d$). With $j$ individuals of type $A$, the expected payoffs are

$$\pi_A(j) = \frac{(j - 1)a + (n - j)b}{n - 1}, \qquad \pi_B(j) = \frac{jc + (n - j - 1)d}{n - 1}.$$

Fitness is an exponential function of payoff, $f_A(j) = e^{\beta\pi_A(j)}$ and $f_B(j) = e^{\beta\pi_B(j)}$, with intensity of selection $\beta \ge 0$. In each step one individual is chosen to reproduce with probability proportional to fitness and its offspring replaces a uniformly chosen individual (frequency-dependent Moran process), so

$$\frac{T^-(j)}{T^+(j)} = \frac{f_B(j)}{f_A(j)} = e^{\beta(\pi_B(j) - \pi_A(j))}.$$

**Theorem.** The fixation probability of a single $A$ among $n - 1$ individuals of type $B$ is

$$\phi_A = \left(\sum_{k=0}^{n-1}\exp\left[\frac{\beta}{2}\,k(k+1)\,\frac{-a + b + c - d}{n - 1} + \beta k\,\frac{a - bn + dn - d}{n - 1}\right]\right)^{-1},$$

and $\phi_B$ follows by exchanging $a \leftrightarrow d$ and $b \leftrightarrow c$. For every $\beta \ge 0$,

$$\frac{\phi_B}{\phi_A} = \exp\left[-\beta\left(\frac n2(a + b - c - d) - a + d\right)\right],$$

so for $\beta > 0$, $\phi_A > \phi_B$ if and only if $\frac n2(a + b - c - d) - a + d > 0$; for large $n$ this is risk dominance of $A$, $a + b > c + d$, at any positive intensity of selection. At $\beta = 0$, $\phi_A = \phi_B = 1/n$. If $a + d = b + c$, writing $s = (a - bn + dn - d)/(n - 1)$,

$$\phi_A = \frac{e^{\beta s} - 1}{e^{\beta s n} - 1}\quad(\beta s \ne 0).$$

**Remarks.** Unlike the linear map $f = 1 - w + w\pi$, the exponential map keeps fitness positive for all payoffs and all $\beta$, and adding a constant to every payoff multiplies all fitnesses by a common factor, so the process, unlike the linear one, is invariant under that shift. Its ratio $T^-/T^+$ coincides with that of the pairwise comparison (Fermi) process, so the two processes have identical fixation probabilities. For small $\beta$ the exponential map is linear to first order and the weak-selection results, including the one-third rule, are recovered with $\beta$ in place of $w$.

## Depends on

- [Fixation probability in a frequency-dependent Moran process](../../../../../population-genetics/moran-model/frequency-dependent-moran-fixation-product-formu.md)
- [The one-third rule for weak selection in the Moran process](../../../../../population-genetics/moran-model/one-third-rule-under-weak-selection.md)

## Expansion

By the birth–death fixation formula, $\phi_A = \bigl(1 + \sum_{k=1}^{n-1}\prod_{j=1}^{k} f_B(j)/f_A(j)\bigr)^{-1}$, and with exponential fitness the product becomes $\exp\bigl(\beta\sum_{j=1}^{k}(\pi_B(j) - \pi_A(j))\bigr)$. Since

$$(n - 1)\bigl(\pi_B(j) - \pi_A(j)\bigr) = j(-a + b + c - d) + (a - bn + dn - d),$$

the sum over $j = 1, \dots, k$ equals $\frac{k(k+1)}{2}(-a + b + c - d) + k(a - bn + dn - d)$, all divided by $n - 1$; the $k = 0$ term is the leading $1$. The ratio $\phi_B/\phi_A$ equals the full product $\prod_{j=1}^{n-1}T^-(j)/T^+(j)$, whose exponent evaluates to the stated expression. When $a + d = b + c$ the quadratic term vanishes and the sum is geometric. For $a + d \ne b + c$, replacing the sum by a Gaussian integral gives the error-function approximation $\phi_A \approx (\operatorname{erf}\xi_1 - \operatorname{erf}\xi_0)/(\operatorname{erf}\xi_n - \operatorname{erf}\xi_0)$ with $\xi_k$ affine in $k$, accurate even for small populations.

## Sources

- A. Traulsen, N. Shoresh, M. A. Nowak, *Analytical results for individual and group selection of any intensity*, Bulletin of Mathematical Biology 70 (2008), <https://doi.org/10.1007/s11538-008-9305-6>, PMCID PMC2574888. Section 2 (Moran process, Eq. (8), weak-selection results Eqs. (10)–(12)), Section 3 (exponential payoff-to-fitness map, exact $\phi_A$ and $\phi_B$ as Eqs. (20)–(21), the case $a + d = b + c$, error-function approximation, and the ratio $\phi_B/\phi_A$ valid for any $\beta$).
