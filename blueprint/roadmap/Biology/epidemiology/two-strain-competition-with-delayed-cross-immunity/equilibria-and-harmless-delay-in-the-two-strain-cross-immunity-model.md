# Equilibria and harmless delay in the two-strain cross-immunity model

**Model.** Let $S$ be individuals susceptible to both strains, $I_1$ and $I_2$ those infectious with the established strain 1 and the emerging strain 2, and $R_l$ those recovered from strain 1, immune to it, and susceptible to strain 2 once a cross-immunity period $\tau \ge 0$ has elapsed. With positive parameters (recruitment $a$, natural death $d$, death rates $d_1, d_2$ of infected individuals, recovery rates $\gamma_1, \gamma_2$, transmission rates $\beta_1, \beta_2$),

$$\begin{aligned}
S' &= a - dS - \beta_1 S I_1 - \beta_2 S I_2,\\
I_1' &= \beta_1 S I_1 - (\gamma_1 + d_1) I_1,\\
I_2' &= \beta_2 S I_2 + \beta_2 R_l I_2 - (\gamma_2 + d_2) I_2,\\
R_l' &= \gamma_1 I_1(t - \tau) - \beta_2 R_l I_2 - d R_l .
\end{aligned}$$

Initial data are histories on the delay interval: $(S, I_1, I_2, R_l)(\theta) = \varphi(\theta)$ for $\theta \in [-\tau, 0]$, with $\varphi$ bounded, continuous and nonnegative. Such histories give nonnegative, bounded solutions on $[0, \infty)$.

**Reproduction numbers and equilibria.** The next-generation method gives $R_i = a\beta_i/(d(d_i + \gamma_i))$, $i = 1, 2$. The equilibria are

$$E_0 = \big(\tfrac ad, 0, 0, 0\big), \quad E_1 = \Big(\tfrac{\gamma_1 + d_1}{\beta_1}, \tfrac{d}{\beta_1}(R_1 - 1), 0, \tfrac{\gamma_1}{\beta_1}(R_1 - 1)\Big), \quad E_2 = \Big(\tfrac{\gamma_2 + d_2}{\beta_2}, 0, \tfrac{d}{\beta_2}(R_2 - 1), 0\Big),$$

and a coexistence equilibrium $E_c$ with $S = (\gamma_1 + d_1)/\beta_1$. $E_0$ always exists, $E_i$ exists iff $R_i > 1$, and $E_c$ exists iff

$$f(R_1) < R_2 < R_1 \quad\text{and}\quad R_2 < \frac{a\beta_1}{dd_1}, \qquad f(R_1) = \frac{a\beta_1}{d(\gamma_1 R_1 + d_1)} .$$

**Local stability.**
1. $E_0$ is locally asymptotically stable if $\max\{R_1, R_2\} < 1$ and unstable if $R_1 > 1$ or $R_2 > 1$.
2. If $R_1 > 1$: $E_1$ is asymptotically stable if $R_2 < f(R_1)$ and unstable if $R_2 > f(R_1)$.
3. If $R_2 > 1$: $E_2$ is asymptotically stable if $R_1 < R_2$ and unstable if $R_1 > R_2$.

**Harmless delay.** For every $\tau \ge 0$, none of $E_0, E_1, E_2$ undergoes a delay-induced stability switch: $\tau$ does not enter the characteristic polynomials that decide their stability.

## Depends on

- [Basic reproduction number of the next-generation matrix](../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [Eigenvalues of a block lower-triangular matrix](../next-generation-matrix-and-the-basic-reproductio/mem-spectrum-from-blocks-zero.md)

## Expansion

At $E_0$ the Jacobian is block triangular with eigenvalues $-d$ (twice, the delay term $\gamma_1 e^{-\lambda\tau}$ sitting off the diagonal), $(d_1 + \gamma_1)(R_1 - 1)$ and $(d_2 + \gamma_2)(R_2 - 1)$. At $E_1$ the $I_2$ direction decouples, with growth rate $\beta_2(S^* + R_l^*) - (\gamma_2 + d_2)$, where $S^* + R_l^* = \frac{\gamma_1 + d_1}{\beta_1} + \frac{\gamma_1}{\beta_1}(R_1 - 1)$; this is negative exactly when $R_2 < f(R_1)$, and the remaining block is that of the one-strain model, stable for $R_1 > 1$. Since $a\beta_1/d = R_1(d_1 + \gamma_1)$, as a function of $R_1$ with $d_1, \gamma_1$ fixed, $f(R_1) = R_1(d_1 + \gamma_1)/(\gamma_1 R_1 + d_1)$. It satisfies $f(1) = 1$, is increasing, is bounded by its limit $(d_1 + \gamma_1)/\gamma_1$ as $R_1 \to \infty$ (not $0$), and $f(R_1) < R_1$ for $R_1 > 1$, with $R_1 - f(R_1) = \gamma_1 R_1(R_1 - 1)/(\gamma_1 R_1 + d_1)$. So the recovered pool $R_l^*$ that strain 1 builds is extra fuel for strain 2: exclusion of the emerging strain requires $R_2 < f(R_1)$, below $R_1$ by a margin that grows with $R_1$. Treating $R_1$ in Eq. (7) as a free plotting variable with $a\beta_1/d$ held fixed would make $f$ decrease to $0$, but $R_1$ is a derived parameter determined by $a\beta_1/d$, so that is not a property of the model. At $E_2$ the $I_1$ direction has growth rate $(d_1 + \gamma_1)(R_1/R_2 - 1)$ and $R_l^* = 0$, so the delayed term multiplies a zero perturbation coefficient and again drops out.

## Sources

- B. Pell, S. Brozak, T. Phan, F. Wu and Y. Kuang, "The emergence of a virus variant: dynamics of a competition model with cross-immunity time-delay validated by wastewater surveillance data for COVID-19", *Journal of Mathematical Biology* 86 (2023), 63, Section 2, system (1), Equations (3)–(7), Propositions 1–4, 6, 8 and 9, <https://doi.org/10.1007/s00285-023-01900-0> (PMC10054223).
