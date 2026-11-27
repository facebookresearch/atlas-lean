# Small-gain criterion for global stability of Hill-type gene networks

**Model.** Let $m\in\mathbb{R}^n$ be mRNA and $p\in\mathbb{R}^m$ protein concentrations in a regulatory network with additive (SUM-logic) regulation:

$$\dot m_i = -k_{m_i}m_i + \sum_j b_{ij}(p_j),\qquad \dot p_j = -k_{p_j}p_j + k_{d_{ji}}m_i,$$

where each regulation term is a Hill function, $b_{ij}(p_j) = \alpha_{ij}g(p_j)$ for an activator and $\alpha_{ij} - \alpha_{ij}g(p_j)$ for a repressor, with

$$g(p) = \frac{(p/\beta)^H}{1 + (p/\beta)^H},\qquad \beta > 0,\ H\ \text{the Hill coefficient}.$$

With $x = (m,p)$ this is a Lur'e system

$$\dot x = A_cx - B_c\,g(C_cx) + l,\qquad A_c = \begin{pmatrix}A & 0\\ D & C\end{pmatrix},\quad B_c = \begin{pmatrix}B\\ 0\end{pmatrix},\quad C_c = (0\ \ I_m),$$

where $A = \operatorname{diag}(-k_{m_i})$, $C = \operatorname{diag}(-k_{p_j})$, $D$ holds the translation constants, $B_{ij}\in\{0, -\alpha_{ij}, \alpha_{ij}\}$ encodes no regulation, activation ($+\alpha_{ij}g$ requires $B_{ij} = -\alpha_{ij}$) or repression ($\alpha_{ij} - \alpha_{ij}g$ requires $B_{ij} = \alpha_{ij}$), and $l$ collects the constant parts $\alpha_{ij}$ of repressor terms.

**Sector condition.** For $H \ge 1$, $g$ is increasing with $0 \le g' \le \gamma$ on $[0,\infty)$ for a constant $\gamma$, so componentwise $0 \le \big(g(p+e) - g(p)\big)e \le \gamma e^2$ and $\lvert g(p+e) - g(p)\rvert \le \gamma\lvert e\rvert$.

**Theorem (small-gain criterion).** Let all $k_{m_i}, k_{p_j} > 0$, $H \ge 1$, and let $x^\ast$ be an equilibrium. If there is a symmetric positive definite $P$ with

$$A_c^{\mathsf T}P + PA_c + PB_cB_c^{\mathsf T}P + \gamma^2 C_c^{\mathsf T}C_c \prec 0$$

(by the bounded-real lemma, equivalently $\sup_\omega\lVert G(i\omega)\rVert < 1/\gamma$ for $G(s) = C_c(sI - A_c)^{-1}B_c$, $A_c$ being Hurwitz), then $x^\ast$ is globally exponentially stable.

The source states instead a passivity criterion (its Lemma 1: $G$ strictly positive real, $PA_c + A_c^{\mathsf T}P = -Q$ and $PB_c = C_c^{\mathsf T}$). Its hypotheses can never hold for this model: $C_cB_c = 0$, so $PB_c = C_c^{\mathsf T}$ would give $B_c^{\mathsf T}PB_c = 0$, hence $B_c = 0$ and $C_c = 0$; equivalently $G(s) = (sI - C)^{-1}D(sI - A)^{-1}B$ has relative degree two and is never positive real.

## Expansion

With $e = x - x^\ast$ the error obeys $\dot e = A_ce - B_c\varphi$, $\varphi = g(C_ce + C_cx^\ast) - g(C_cx^\ast)$, with $\lVert\varphi\rVert \le \gamma\lVert C_ce\rVert$. For $V(e) = e^{\mathsf T}Pe$,

$$\dot V = e^{\mathsf T}(A_c^{\mathsf T}P + PA_c)e - 2e^{\mathsf T}PB_c\varphi \le e^{\mathsf T}(A_c^{\mathsf T}P + PA_c + PB_cB_c^{\mathsf T}P)e + \lVert\varphi\rVert^2 \le e^{\mathsf T}\big(A_c^{\mathsf T}P + PA_c + PB_cB_c^{\mathsf T}P + \gamma^2C_c^{\mathsf T}C_c\big)e,$$

which is at most $-c\lVert e\rVert^2$ for some $c > 0$, giving exponential decay of $V$. Stability so holds for every nonlinearity with slopes in $[0,\gamma]$, not just one Hill function. The same Lyapunov function, augmented with parameter-error terms, underlies adaptive control laws that steer the network to a desired steady state by adjusting transcription rates and keep errors bounded under bounded additive noise.

## Sources

- Y. Jin, M. Lindsey, *Stability analysis of genetic regulatory network with additive noises*, BMC Genomics 9 (Suppl. 1) (2008), S21, model (Eqs. 1–6) and Methods (Lemma 1, Eqs. 8–10, Remarks 1–2). <https://doi.org/10.1186/1471-2164-9-s1-s21> (PMCID: PMC2386064)
