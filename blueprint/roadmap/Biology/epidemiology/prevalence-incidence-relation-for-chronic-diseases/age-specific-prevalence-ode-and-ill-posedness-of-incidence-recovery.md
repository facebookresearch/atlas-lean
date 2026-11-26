# Age-specific prevalence ODE and ill-posedness of incidence recovery

**Model (illness–death without recovery).** Let $S(a)$ and $C(a)$ be the numbers of healthy and chronically diseased persons of age $a \in [0, \omega]$ in a birth cohort. Healthy persons acquire the disease at the age-specific incidence rate $i(a)$ and die at rate $m_0(a)$; diseased persons die at rate $m_1(a)$ and never recover:

$$\frac{dS}{da} = -\big(i(a) + m_0(a)\big) S, \qquad \frac{dC}{da} = i(a)\, S - m_1(a)\, C.$$

Let $N = S + C$, $p = C/N$ the age-specific prevalence and $m = (m_0 S + m_1 C)/N$ the general (population) mortality.

**Theorem.** Let $m, m_0 \in C^0([0,\omega])$ and $S, C \in C^1([0,\omega])$ with $S + C > 0$ on $[0, \omega]$. Then $p$ is differentiable on $[0, \omega]$ and

$$\frac{dp}{da} = (1 - p)\,\big(i - (m - m_0)\big).$$

Moreover, $(S, C)$ solves the illness–death system iff $(p, N)$ with $p = C/(S+C)$, $N = S + C$ solves

$$\frac{dp}{da} = (1 - p)\big(i - (m - m_0)\big), \qquad \frac{dN}{da} = -m\, N,$$

and conversely $S = (1 - p)N$, $C = pN$.

**Proposition (ill-posedness).** For given continuous mortalities and $p(0) = p_0 \in [0,1]$, let $\wp : C^0([0,\omega]) \to C^1([0,\omega])$ map an incidence $i$ to the solution $p$ of the prevalence equation. The inverse map

$$\wp^{-1}: p \mapsto \frac{p'}{1 - p} + m - m_0,$$

which recovers incidence from prevalence data, is discontinuous when $C^1([0,\omega])$ carries the maximum norm: estimating incidence from cross-sectional prevalence is ill-posed in the sense of Hadamard.

## Expansion

Differentiating $p = C/N$ gives $p' = i(1 - p) - m_1 p + m p$, and since $m - m_0 = p\,(m_1 - m_0)$, this equals $(1 - p)\big(i - (m - m_0)\big)$. The equation lets incidence be read off from prevalence (cheap cross-sectional surveys) plus mortality data, instead of lengthy follow-up studies. But differentiation amplifies noise: with $m = m_0$, take $p_{\epsilon,n}(a) = p(a) + \epsilon\sin(na)$. Then $\|p - p_{\epsilon,n}\| \le \epsilon$, while $\wp^{-1}(p_{\epsilon,n}) - \wp^{-1}(p)$ contains the term $\epsilon\, n\cos(na)(1-p)/\big((1-p)(1 - p - \epsilon\sin(na))\big)$, which is unbounded as $n \to \infty$ for $\epsilon = n^{-1/2} \to 0$. Practical incidence estimation therefore needs smoothing or regularization of the prevalence curve.

## Sources

- R. Brinks, "On characteristics of an ordinary differential equation and a related inverse problem in epidemiology", arXiv:1208.5476 (2012), Section 2 (Theorems 2.1 and 2.2), Section 3 (ill-posedness of the inverse problem), <https://doi.org/10.48550/arXiv.1208.5476>.
