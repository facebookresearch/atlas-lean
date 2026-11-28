# Influence and determinative power in Boolean networks

**Setting.** A Boolean network has update functions $f_i : \Omega_n = \{0, 1\}^n \to \{0, 1\}$, $i = 1, \dots, n$, and the state is a random vector $X$ on $\Omega_n$ with an arbitrary distribution $P$ (not necessarily uniform). Write $p_\omega = P(X = \omega)$, $X \oplus e_j$ for $X$ with coordinate $j$ flipped, $\varphi_j(\omega) = \omega \oplus e_j$, and $C_{\varphi_j} f = f \circ \varphi_j$ for the composition operator on $L^2(\Omega_n, P \circ X^{-1})$.

**Influence and sensitivity (Definition 1).** The influence of $x_j$ on $f_i$ is $I_j(f_i) = P\big(f_i(X) \ne f_i(X \oplus e_j)\big)$, the average sensitivity is $\mathrm{avs}(f_i) = \sum_j I_j(f_i)$, and the strength is $\sigma(f_i) = \sum_j I_i(f_j)$.

**Proposition 1.** With $T_j = (I - C_{\varphi_j})^*(I - C_{\varphi_j})$ and $T = \sum_j T_j$,

$$I_j(f_i) = \langle T_j f_i, f_i \rangle, \qquad \mathrm{avs}(f_i) = \langle T f_i, f_i \rangle, \qquad \sigma(f_i) = \sum_j \langle T_i f_j, f_j \rangle .$$

**Proposition 2.** If $\Lambda_j$ and $\Lambda$ are the largest eigenvalues of $T_j$ and $T$, then $I_j(f) \le \Lambda_j\, \mathbb{E}[f(X)]$, $\mathrm{avs}(f) \le \Lambda\, \mathbb{E}[f(X)]$, and $\sigma(f_i) \le \Lambda_i\, \mathbb{E}\big[\sum_j f_j(X)\big]$.

**Determinative power.** With binary entropy $h(p) = -p \log_2 p - (1-p)\log_2(1-p)$ and mutual information $\mathrm{MI}$, the determinative power of node $j$ is $\mathrm{DP}(j) = \sum_{i=1}^n \mathrm{MI}(f_i(X); X_j)$. For a set $A$ of coordinates:

- (Theorem 1) $H(f(X) \mid X_A) = \mathbb{E}_A\Big[h\Big(\sum_{\omega \in \operatorname{supp} f} p_{\omega \mid X_A}\Big)\Big]$, where $p_{\omega \mid X_A} = P(X = \omega \mid X_A)$ and $\mathbb{E}_A$ is over the marginal of $X_A$; hence (Proposition 4) $\mathrm{MI}(f(X); X_A) = h\big(\sum_{\omega \in \operatorname{supp} f} p_\omega\big) - H(f(X) \mid X_A)$.
- (Theorem 2) $\mathrm{LB} \le H(f(X) \mid X_A) \le \mathrm{LB}^{1/\ln 4}$ with $\mathrm{LB} = 4\big(\mathbb{E}[f(X)] - \mathbb{E}_A\big[\mathbb{E}[f(X) \mid X_A]^2\big]\big)$.

## Proof depends on

- [Jensen's inequality](../../../../MeasureTheory/integration/jensen-s-inequality-for-integrals/jensen-s-inequality/jensen-inequality.md)

## Expansion

Since $f$ is $\{0,1\}$-valued, $I_j(f) = \int |f - f \circ \varphi_j|^2 \, dP = \|(I - C_{\varphi_j}) f\|^2$, which is Proposition 1; the operators are positive, so the Rayleigh quotients lie below the top eigenvalue and $\|f\|^2 = \mathbb{E}[f(X)]$, which is Proposition 2. Theorem 1 is the binary specialization $P(f(X) = 1 \mid X_A) = \mathbb{E}[f(X) \mid X_A]$, and Theorem 2 combines it with Topsøe's bounds $4p(1-p) \le h(p) \le (4p(1-p))^{1/\ln 4}$ and Jensen's inequality for the concave power $1/\ln 4 < 1$. These formulas extend the uniform-measure results used to select the most determinative nodes, for instance for canalizing update rules.

## Sources

- M. T. Matache, V. Matache, "Logical reduction of biological networks to their most determinative components", Bulletin of Mathematical Biology 78 (2016) 1520–1545, Definitions 1–2, Propositions 1, 2 and 4, Theorems 1–2, <https://doi.org/10.1007/s11538-016-0193-x> (PMC4993808).
