# Impulsive limit of short mosquito releases

Let a scalar state $p(t) \in [0, 1]$ (for instance, the frequency of *Wolbachia*-carrying mosquitoes) evolve by

$$p'(t) = f(p(t)) + u(t)\, g(p(t)),$$

where $f, g \in C^1([0, 1])$ and $g > 0$ on $[0, 1)$, and the release rate is a sum of short pulses

$$u_\varepsilon(t) = \sum_{i=1}^{n} \frac{c_i}{\varepsilon}\, \mathbf{1}_{[t_i,\, t_i + \varepsilon]}(t), \qquad 0 \le t_1 \le \dots \le t_n,$$

delivering a total amount $c_i$ in the $i$-th release. Let $G(p) = \int_0^p \frac{dq}{g(q)}$ be the antiderivative of $1/g$ vanishing at $0$.

**Proposition (instant-release limit).** As $\varepsilon \to 0$, the solution $p_\varepsilon$ converges pointwise to the solution $p$ of the impulsive system

$$p'(t) = f(p(t)) \quad \text{for } t \ne t_i, \qquad p(t_i^+) = G^{-1}\big(G(p(t_i^-)) + c_i\big), \quad i = 1, \dots, n.$$

For an additive control, $g \equiv 1$ and the jump is $p(t_i^+) = p(t_i^-) + c_i$; for example, the sterile-male density $M_S' = u - d_S M_S$ with $M_S(0) = 0$ becomes $M_S(t) = \sum_{j \le i} c_j e^{-d_S (t - t_j)}$ for $t \in [t_i, t_{i+1}]$.

In the high-birth-rate limit of the *Wolbachia* replacement model with wild and infected mosquito birth rates $b_M^0/\eta$, $b_W^0/\eta$ ($\eta \to 0$), death rates $d_M, d_W$, cytoplasmic-incompatibility level $s_h$ and carrying capacity $K$,

$$f(p) = \frac{p(1-p)\big(d_M b_W^0 - d_W b_M^0 (1 - s_h p)\big)}{b_M^0 (1-p)(1 - s_h p) + b_W^0 p}, \qquad g(p) = \frac{1}{K}\, \frac{b_M^0 (1-p)(1 - s_h p)}{b_M^0 (1-p)(1 - s_h p) + b_W^0 p}.$$

When $1 - s_h < \frac{d_M b_W^0}{d_W b_M^0} < 1$, $f$ is bistable with zeros $0$, $\theta$, $1$, where $\theta = \frac{1}{s_h}\left(1 - \frac{d_M b_W^0}{d_W b_M^0}\right)$. Moreover, the minimal cost $\inf J_\varepsilon$ of the outbreak-size functional $J = \int_0^T I_H(t)\, dt$ over pulse controls of the above form converges to the infimum over Dirac-sum controls $u = \sum_i c_i \delta(t - t_i)$ with $\sum_i c_i = C$ ($\Gamma$-convergence).

## Proof depends on

- [Gronwall inequality in integral form](../../../../Analysis/ordinary-differential-equations/gronwall-inequality/gronwall-inequality-integral-form.md)

## Expansion

Outside $[t_i, t_i + \varepsilon]$ the dynamics are $p' = f(p)$. Inside it, compare $p_\varepsilon$ with $z_\varepsilon$ solving $z' = (c_i/\varepsilon)\, g(z)$ from the same state. Both stay bounded by Grönwall's inequality, and $|z_\varepsilon - p_\varepsilon| \le \varepsilon M_f\, e^{c_i L_g} \to 0$, where $M_f = \max |f|$ and $L_g$ is a Lipschitz constant of $g$. Separating variables in the $z$ equation gives $G(z(t_i + \varepsilon)) - G(z(t_i)) = c_i$, which is the jump rule. Between jumps of a bistable $f$, a solution that avoids $\theta$ is monotone, so $F(p(t)) - F(p(t_i^+)) = t - t_i$ with $F' = 1/f$. Differentiating this identity and the jump map gives closed-form sensitivities of $p$ (and hence of $J$) with respect to each release time $t_k$ and amount $c_k$. These sensitivities drive gradient-based optimization of release schedules.

## Sources

- Almeida L, Bellver-Arnau J, Privat Y, Rebelo C. Vector-borne disease outbreak control via instant releases. *Journal of Mathematical Biology* 89(6):63 (2024), Section 1 (equation (3), definitions of $f$ and $g$), Section 2.2 (bistability threshold $\theta$), Section 3, Proposition 1 and equations (8)–(12), Proposition 2, Propositions 3–4. <https://doi.org/10.1007/s00285-024-02159-9> (PMCID: PMC11557670)
